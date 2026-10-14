-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0481
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:01:55.853152+00:00
-- url     : https://prove2.me/submissions/166254dd-7d36-4a0a-a754-aad669c648f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 86330936 ≤ n < 86510792 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 86332186 1250 86330936 86330987
    0x1060e0319230609070906140d140703050a0609050c0102011a1002010b0a0605130e0105010903080702060c0a060605040e0610030b101a0301030b070305150111030c06010e0601020c01 80
    0xb580814108118141100303410701c603190780c812004010740d0b4070607040c00d00101607240c50104280c1c02c07035109030031282d50200d11311300301d00786c0c2e481d5143e558211136400071281d26503101484886041c0040c1d40c00091003401100c43d15420701a440c0c100741c02141c01031050750303105024040103a088030040d808030700001040d02c022f400c040c5402c20304854001c68500000c80c4440c00940010094030b00e0380c100c2030102d54080ba03c0e070108504161200c0203845554003402c855414040080c00d43d04892100a0016100240000454640030141c40940c0303a030204452201c1010b20b81100540014007959000300e03d044100540000000703103060180b00c00ca0400d81d007590442d182c14200600042c1405d52160304040c0000301c203101e0419051840031a80d900680b25419440d002c8103030170b4046c00040130113007031009004514407181c2050244d0302c0e09003411400307581c0316500c807420341c011006510000d00030403000040c51001031080b02d218074000da00340c1c0c40d02d5507030f900151981110300103501403200720380b00e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 86333436 1250 86332186 86332193
    0x1101090816150905091f06050406020613020d0b0a0f050c04030b041103010902030a050d2c1306180203040510020309030313030c0b01081c0201061a13030c0e01060e0319 74
    0x120b0514162034030b00040301c1600d0b1030100d403059100340e54214440600d424140400d012448410700544201c1c9003841c41e140c5820303002136481c0c502410126100d40c1440b8403d085540d81088020324a40c80b0000d10010300d05103485400402c518946102da4a041400041040f007034182120152644100c840000b038989880791100c0100135244d4940540d40c0b104210096a030801084110f0341c4244020310380710fa0350307040003403081c2614082030590030407920f0001221540051002c42042040c1c80d01d194640042180d900540700c580d0141d95064090810b03100303a903240303030015803040e80070380211440da41d80741900c58100c1c03204558900ca186c1007440400c0c1c007209121200740080f4041d00d054107540401e500d0f120300031003080c3e11114280c0d0040303100e50750308038450340414201c012030300007040014903001e202c900d40e80640030020405540018084d00035013801044402650f0045400d0005035140d1303040030390810b030a001d091701140c0388076420015403500062084c1842c0b100b06070707032020b6500c82e503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 86334686 1250 86333436 86333459
    0xe01060f090b060f0f03040309211202121602011704020a03230d0f0f020616180801091103120403050309010c050a1a180f030f0306030a050105041101090816 69
    0x302d035030049040002c03605032150f82c0080e100d01240d186001e41e49050038500544203007500e600203100c240500e8819005d4959955072004c0e56038111174a10760b80c400c5004100d0808440021441c501140400c254091303e2414103184604d61007038840f0342c0030042c2032844200d1054201c4009600c41c940700000e00020390725590f0881301c4071120500710246140603283d1400d0002d600800030001e04070f00c580140b01c0c2d0b0303c0200c20700c142c210b60000d0190303820300350004100420201034080510000c2c400260f00580a901410028808203008120b103505502d821840000b1070000c0034071038030501003e02c0603a01503030216021207a11400942c9441181401511740c2c000d1144195038500075000341c840032a1020380c580302c07820049040f40e00b00740b500304200c00601c0780403501d015099004000e4000d514038000210781c113003941074103880c2d2aa82d58034002450062a0100180b1a50034582444200001c400758410b0b9203609803200d018a80d260034a4a68806800342d440c2040c40380300ca4100949a0480d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 86335936 1250 86334686 86334701
    0x101104121b0305030301031a13020310020a230d051602070501080a0f1404120318022b060e01050106030216031826060603062806180b040e01060f09 65
    0x11500c0307040c05035698a402c2d0a54200b41e10569240414124059140058072169503004282140d030381c10390b8440381c010031b541d804038113101030020343e002480c4410f43e40921003503120780011410107074034020b112504400b80d400140c2c140781da45080c080400c0000c1e13441c0840318401d049039802050054600030044440c403001400b418085a5141301d80c10760340c1000d01407008a4078141d080c01c100fa00f8640b82540f000341025000f00105450052080ca03114100d450b001034140c1c0441d010824101005c400100c0b04564a0740c102e034080c94210008c0400000da000021880c40703400080005a980382d0040e41648a5141d00d05c04c0c007810111142d0000b4001c43e4400410900b11007594201521003160250b15010310007003003140210b12007580c01a5404000d52688500d00307902034115424903a03203c00e040d01c0180ca40783c0808550130fa6441c1402c806a02010083c5140000042840540c0c20720000a2510019240c0207504101401c0e004c02d10502030001251902e01c81e580803180382640c96030080800c2c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 86337186 1250 86335936 86335973
    0x60503040605190f09110901050f0409110429010c170c0c060d2c03040b070f020402030a0506010e092211131d010e0c0d081204030210110412 62
    0x20303905070904401e051322a804c40f00c0c01c00c000010b1060203a0402c03840700d42613410b2541c85040b4070801072166440d88402203440c1d4030255000b061150b0f041c03070058540c60050a01075041450680b5200b070160b101c640383c0c051031440d81116400c0401031401110616040074000e032146e03641940000100c94a100186331049420060b030b90a014948d0006690b98880315a02000a0b2500c82d4402c9400108049050056038072802490302058200080d499008034416503409080209a80d0103020078102105441ca600400440d520320f0955289001007805641242c0044c0960025256500b84884501c0c003441080f5020740552031444010950059441001c50765175094103081074807512800700c01c1701c481d60070300d4020071001056040300c0c810807a00e0303549003040d0781051003e900d07843c00460803ca900328180e03004003c00f2128103080d41140b28103044100b070039882000300401d156001c41c240091540c0c4600500c03072082c03456585c2c8180d010f00c2c081c070300e0f0305e0185940c0b07400011000322000d00d91642 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 86338436 1250 86337186 86337211
    0x30316021f0503100f0f120507170a03030c05070b0a110d1103070212070305040b0f0f1201060f020f07120317010605030402030c1507020d020402040b040909050d0306060503040605 79
    0x28802800d40c0007030206003031000c50804400e02141e05540b1003c0d0018007900c8486101161410b10110802d0015214004030340401c0340110341030110074803900000c0c000720315070500d400760b9003280310340c1c0c4040e121410360001780b03044c65510401d031080003150200c50b045620300c403040c0c907002c2c41032006012070080c02074103020401c110300740d004060260012500c426281c07191030b440e10480c0a070030801140303280500c0314010040b9200081d0400c0641c0c0685055295032074481c4001001d0705034030712032103044241c800e1002c00c840c507183c00084081810b0320090742e00c0c07102d040e1001c00c4c16a03583c0e0010080d00d4464124140038801650700180d21f9401e24081d00d4114150614044040300f540300a07045000000c1e800030800c025402e0410404a070004280d42c240c0b5554030404a543d00c1c1c0c0a800c90082c403415240380140290f58440c4c05880283c48a07069655a841ea100c0d440c40c01804805011542070040b42d5540c80c145019210303160442d08503031070709031440da220368440c0020300009206070720611 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 86339686 1250 86338436 86338459
    0xc2401030b0a05450606010c080c0316050303060103110405060706090f02060307080106080f072015090d140304050303010b030c0c120405010201140709090b060919030c080a0203031602 81
    0x74100415904c000801c035211890072510104c2089000c150444000066110030140009640d2140903c051182c1181059445100c4482c0c00b5085101d00f0302002d00001c503041c00c8805220300800154000d1000340c07410040c04285400c423007031902035886680c1d4004000c0c800e04004c200e5139040003408a1003103880e000b004141e0341c00034042c7c0e0400d0300c0c00d0340029550300043c00040d800c881166088a229501000c0034a0300d014024200c2960964048102550301440000f100b810404d400c0b170008050914502454690150703903959281d500c0c4040020403805010412060807070440c1e01503a0040e0140d031131a07007400700644843d413010f001825042410064024840030502c402e00f020300501c900c0070703074403490440020309403150425082c2035049002c050103000c58203d5050422240040030206940c1d450400040035401142521a0007038140c200002000054681c003109580c400d5030b4017481e450300c0b5299195104c0020b031000350194020005124184a1803500c003040c544000d0910007642c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 86340936 1250 86339686 86339731
    0x3060b0901030b0d0605010305010207140111030636061e030d0305040c090c02010b0405150306071b060204090509010c0206070807081801020715050106032a0e060c2401030b0a05 78
    0x1286c00b43d0081d102a54041040000c2040008048040c546020000d002156071818a0300180c8405000c45100744003190844600b29a801680c40c0c0c1000f031411040d881e00c1894415440c00f40e03007100e05c240b050807401c5040580c409882d080a141e408051b004000c0144600010350050001030000d5524200101001a0101c0503029070000781046500215241e03000c54240410f030b440c094401291a1290900401e841d1400030380d1540c1b041c03803450400607002d90f6120312100c8011140300944001e000203404150880c01c3c0c0c1005000e2031281c002040908605e403000c907240c000c1030b51182c0004036468040384d1050700ca0b56403d504004402c1480304074912007180c05089a0004404585042e400682001c0307211a0748030b4503004145909007030011450221400421030200300d01400c04840c04014a60080e12496405a081e170300500000e66580744480039a40c0d803041a04040c10b00c20140ba100da40c40050b012a46040b0b95001442c1141500d4500740340015200042518580c0e6007000d441e04d082 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 86342186 1250 86340936 86340941
    0x3030906070606030308010e0609040b04060b06070309030c0605030108100c1b0f0b0903090f04050c07050105010b0d0e0d080601031a10051305060a05070209150d12020d03060b0901030b0d06 83
    0x400e442020b0002e281481c501e40034014610580c8081d1b0141c254500b000310640310000004e912030743c0009201c0d0580c1d03c0785801d100910584a580750403a802040764020550058414001d0301e008034040109175079a00d900f1290703072009000f600281e400254540c50401e100b90031025681d1010308002c1c0c40e0544c0c0700108a480050803071305950708840da840c494203024031244802e80008100f00618900400d220100e2078072552040c2c0746015071750b07940003d41d440700a1802d0f01d0400fa1f03c000284841e5075100d41b0000e440e00a018401780f168545104011400e000094441e051802030f1030b003440795550600158001c0070302100004111082c04800792850382c5219440e02c0c000d0712505c07202d8440405402562166440c2d410044c080d80741000340e010503540120640361800d504440360103003651504949200305002441e61a04503d42c0300c1040d040180c0200318086102060f400c880070301000c44402c409881c968032030b1034442642041039100347d520a801c088510a4060214107185c801c0f036603440308 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 86343436 1250 86342186 86342197
    0xc080a030501140109050306060121090302030304021309021e0103020706050f1801060503030405040b03070b04240c11130209060d0b0411031b0a12020703020c01140c06041103030906 80
    0x1a941d6001801111185140710b62009070a10309980b0071810800425624900500b40314180045802d12044944130603010051959070090144050340062601940e02d400580c0c3c00c0788200100c0741c2046940324284144140e00e50004c0800c1c61040d084100b500740c440c40c42e618141003580030881c20010031118050b8601507903032000664498036001c804d0300110b489a243e4031901c1e0341400002c01c003e903000405d40742502c03c1140c0000740c0c2142000001d00c0e01c103884c0c2c890300d0410380106e000078242000ea03090040c0d00d0b00f01400401c48140c80c0b88112200c030302e00d01d40104410010548070560b802c08440c1c16800f1140340b03000528144c0508001805a00145d9162140c80d40742e086401290500b4060300c01e068005011075421070811aa41c0304c4100e0480c2043c001c202c1c804503642503802c3c403580b00c4807050759a03000115a541c0a50a00945035015a209a0301140e42580b1000780710300f00320100c0d42003240c03d401900c0317181c42e10340c1d890075000c5101032400e1b41440309026592040ea5031000411 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 86344686 1250 86343436 86343457
    0x30c1403040f0819080405390609130510050d0b040605070221090307080607020601030f08040506040612060506040506070605090a0507061707030204150f020a0b01090f0605060a0203040509070c08 86
    0x203e10b047e103421458481d400320f0b5841303400340700384403450307401011196003020700800b502c0348034544180c00118040e401127503070b403607441403000341000b00c00d1140383d100070f0051945281010809448005010030003a608000500388607440b400034010804135484140c018003948190741c01518680c64482000c45180b0104441890008030500c00745000c1003060010290103010f000c503031602e01c0c4040e4a41005100242500c500b49074424104492101210081e01c0001c10494540c0c0d241c00c401024041d022030403202c900d14042000c00d00340703800c2003034508032040241254034101103551604042c00000e070800e40140301e5012070a00198042c056040505031590314082420174251608880707850185c800018184100300034080c1560014007612540d2103420074070040a07507807000f02c4c0740608100c0c015000740340000000c0703209105600004214500e4960500103140c035442048020b2064222810140c3c5c000c0204205900b4600390a69200145040200c2182c08079240c14039554056118074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 86345936 1250 86344686 86344697
    0x1060e0a0306050a140a06081f020705071202040b0d2f03060c03160306031e030e0307060e0307080712140a120905091608010e0c07080706050403030c1403040f0819 72
    0x3001c0300300000341740b5034000c42c00702e4240301442ca040980c07500d4000b5540300031403486001c080340c00301003440e40403a0132080c1c1c03190480c2d841c1c40e030f0b42c002080c0d99400d0180803807041b8184882000c07145862407145403140d82201c000c0e403880c0e40c01c0e1196510107407040800c4418001ca4002c1180320341d824002244101d03a0003850656a24180303180180240c00844458141490040c00f40041040910b030b07020380c50315981142031b10310558103054890410b1160302035454801c1800114071190300c00d00c1c5508121042d8112140c180e140c0d141c0644070400c034025000500c0c00441c0b0000460000001042c209100c002030703521000c0140c0711611018100510f80000c500590b07010002d81c01c4c0750042640c0070030a00001c0010040040c0014062a410701c01d4007441e84040d00414a0180600c086a420381e40c01030030a0390340c0800c0c0c50107001510040b203098010034a800151804240a0320550340c0500000c86858a117580d1079031401d0f00360146202c180c03402c40091105141c40a10300c159541078041c992501c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 86347186 1250 86345936 86345951
    0x30609060f1f050f04090f3005030c0d021917060402071e02010908030d051504060302010f0c11090903030406061a1b240906010801090b01060e0a0306050a 68
    0xa22503900025011a01003000881c81d664680b0014a0300c400307503102100e841c0c200d0301902c4002409040c8203030000e000707181e00802541c1081b916130302d10a41341e2001061124030300e00c2e60000c1001d0700c0072082240d01007a01080000c500813096001054182c1c80301600600700341446004c0c1c40340d266034002c5500458618030700918130242c680003155112038115015450081c0a40e201d9031016902c0b0341031880c2c080c22281950440e8095007000000e803d86404483e00c503955855110003501040d074000b98092861345078010075040078080c0710f050340c3e0180c5501d241c0d5442c030601210380c0c8186420555481842c4061032519a0352094042d00550380f100085403281002c1c14002d080b141130b544550800168a513100c0311101c1e248082e500528007038900e441c01c410b0810346144c24034299003120400c820317440381c0c0c50032086803110700c03180120102000c607a1030360380340d800141c202d8045801c05018042480010000c00b88074180c100e5075524050052011195a681d810050700c106651002e42e00703488191 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 86348436 1250 86347186 86347201
    0x1605090a09050f0307060f1a011107090e0109020909010c23040504060303090504051501120b01021203090d020610081209030a02030d091406090603060f010507080403050105010f0e07080609070e03060906 89
    0x10300e4010f0341f442400700310380e51440604103000802c81911905000d01d03103c0f0740030010340a110060051031869000e101660810103d10700900000074124402c03404280400c401c584148107450b5440f40035140e0310074101d0341800641480301803000468400400b04070201e4140c4850003620000c500c00d4507261740355410a400c1006a07407000384049000d03c01c85428135102d030b9000e42080405c0d42c2070380001a2440264004078141892625011107199001060215010001904403000005a801c0d02c1c004d071100e45d40204d10003064407079150940e0041968401c184542c070003d2203117181c02006c45079036524a6011904080481c164040445c480c01c030104540c0c00f100c607410800d251304607411803a01302e00307000051007404003800903801400010003003842070740500c0c00c8130003070b5401c80d0f100c54a483c0d40c0c1c80c1942c0644002d000b2221000405040000c910f04a090a280200816150140255a41c50a000003503500a0180c0304100400000702c45a4078280055030080003030002518030380c0340c17542 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 86349686 1250 86348436 86348441
    0x30e2403190e07050f040e060c090a0b03160302130e0a0e1002070302070e060a03020a0f0503011803020c010e030c0a030602040f080307020108040f0f0b01090903030e1605090a09050f030706 83
    0x22190740c41c1c50901900042e2948003003110710555000320b50314808000070002150081008900c1c60245208034814032003003142c2c0d400076002c003040865545403072544642481407031703000941f43c0c0c41032201851010b05c845d60080c0c001d0110360f07403d00402c9415565410a2426280e820354450300e8050340d85803240800c070b1062100442a00c416441540303040000c0d42c000399102058890140c210210340041100c580d9600358400056400900c0c09921580360980785155a800b4803803517101c4d41c40d01d007480b100a4826180040c0c0160160083c0410240e6072005480111043c00c24a1b4136008a8a51084c41c1c0d5507003016001550050f00c005803114285540c801d41082182c00920392079200707118110060303a0045940e41c1c050740c010000c400d0b034105d5107001905000c440800501c10744036400040b42013503982d40011486402035a00b0b20000d107191040c1e644035281452200600c5c510143c0500032070030040c0d17285411940c5240c0009031004c094482600f002c4500704240d8070b80d0000074092007401882d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 86350936 1250 86349686 86349721
    0x1905030615070821271606020d080a1a0906040f0c0509030c24220303050702040b0a0e070509130501030f14030f04060c11090108010c090e010503060103030e2403 71
    0x4448130802e0b82040c100d140246034164915556440c412005040700c1c030f5041c00202c6540c0c44040079610101c0d15040044c2d207980c11202540300049400340090707550f1889000d076401c030484889806481102c02018000e181a008000b1a00a6220600c41c0021111842042310747d0000da90f400f510303403102104240c00e042e050381205101e4102209628400080c080c01805410402d441c500e81e10b400440040310416a00d03c1400d4110404400020a040e080001071034424802c403000c0140e070117100304211204606020390341100c9141c100159010f030145009100e805001812507480490300704400050b101c00340c00071600361810342044010020072240039008083c250001d141041d0356010501c120307014910502d41005100303907a180501141c2e80d40c19045040c05011000389607100d02c0e0449c0a01403258080c0c0000703074034140008400c0080300c81c0605a4030001c01034202ca0b403031501c0891301030034048002030303000718508a149901c0c440c4086115017144424841c5440740b500804800850000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 86352186 1250 86350936 86350987
    0x3010518010b0a1b1205030a0f0e070302040506060d0912020d0c0f030804020a050916020d050a050d020a050c070320040627060b0c0102091519050306150708 69
    0x1950041c0105452107003516440035040c680344c0c1034803000c046440c2e80102c200b00090300906889400c000707142ea101e0005c500c83d2140d51028000088441c0304442260301a80007200903400c91a020f00044c68150401604910024041c80c01c0100300724582c070444400d00e90880c0c910a001c8041400c541e01840516283c4559041144600203151a400760751000014003c081044034030000e401c560322a140d02025100c0503004184034605000c0403001c0c0980d41408501504c100e903203001c0d0b16441042280e51b0040c03103596090401d03486040c8039000e03400c0031064106020081c0000303c110a8100030b000019030207204404034950200000c111442d01c00180e403400780d03003407450622280b800321050002c1c200100350000300355180903040400510f502e4006da65013a0700000d07040881e0760150060521749030202e50500401d8500d050100891080180e40030307030700560b00b140050890244c03003d5603010201034442800c03442088080441540070305402c0350400d00120313000c0079040350500e2000c1c1d048079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 86353436 1250 86352186 86352229
    0x20109060b0301050118200a0e010212030606040603150302041e0f0b06191103040f030c0902070b06100201020403150606030f06030213090c080106120528020607060b1302030105 78
    0x103001c501600c80e94030081030744056465020714154a510112087c103c0d6205580c05a1078194941004000406841c2c2941c018480d504020850311011030840f4055800100081e25003031828906402501d042501c4000f940386083c2c000003d40c85a004440a6002c01440071480f01007465110781122040300c0f4041c610744c80c1441c100c0c400d4542c4811120300c608030508205008500980c2101d05c1010303255401e5103800045800251218001101c0d0140ea02c0783c5228500c4545680240049026800c8003411800b600408a03a29051009003008a6007a510000d403515031240c50322006244095030641140b540c544040240035403610030b80070840c03881041031007200d2668000421200c04690300c035140c82d903205000c2e010050075078140d2000b8030100c0000c0c40120340d6070340f040201b4060b6017803d0303030a0f0280d00c0d1948a100e00440f4282c40c0e031304000a40782c148803007540034002e0744d8010000480300907946071a000065643d60600e50035640c0b1740080940c0e00e41c108018011044030000f1a01148203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 86354686 1250 86353436 86353439
    0x1b08060f07090515031306090c1a070b0103030c0201020a0501021207030501151e030b040e030301031e05070605030a020708030f090d090503030d0e07270b181b040510020109060b03010501 82
    0x903100c480d8110010001e0340001c1d10382c0c842140340a1001c480700f40061030030745400000c41c1048483c02003d41214080c1001043e15003401122182c94452f000004103aa0f28107001440064065010380406e00d0041c41240e0481c9829034480d4220f030702045410910100c002c080203101a85401424094010822007140e807180c1c003540903144107400f090795032098800500c610010343c031035481b2095140d0010800e100e100c0444804a40300e6000707020944031001400d02d40300018001e2059050007591220041c003005240c070004480d1508003070400d4112030303000c00454001ca00e100f40030354002c000c1e0208880150074400800e9180c608481d14180902c0788002c8200140e0380c010050b180c1c140d081c01400300380e141c0c260f4242400c24101e900000031209004e412405151200715604091801100042018a0218007046000705c45000c050790040010000038521011041c0d0403440364566010090030151038030700249406803110f680d440107039503030001d140030302000d40112042040c05170002c000d0755 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 86355936 1250 86354686 86354689
    0x5010903050d0e030f03040303030f11042102130221100803090607080d0501060f030e0714010c02030a060e0c031c02070302061b0304030b010e071d0d1b08060f070905 73
    0x488a5554003802d003c06800003070744075201030103c82d044030840c00c1641d5485450f490003038000d00300d040c00ea41c469440c03c06042c543e540c142085409032041c20a14450783c810101e04d8000c9450824000c0340c1004d01c1d616060300074041800944100c9402c1c1b09004803280c03403840c40d405408401400a00741c0ca50041c0c04114501012049450011050310480d80d10881400c10b070600348102d00e00c4020645c546070000810b1540707e10584210402c030b40e41031200c448040f00e2130350780d0307038460041c88626008645440b902e58029034028514903c040c1c00d40c1c00e01d02054807180105c400d03400f414052a0070110b42038080e0702d01030182c0501982018020014490140002075403445030303000090103407500003040c2c1203010000180740614071601c4c0803030703030380341e8a80c034200515000a100700c006175902030000c265800d001e0340f01c412a0b82c10040e0510740c8051541e0810140030021074042e29810704025504202d1156070540d403002d84050740050046041485110121000041c0450708100c42c0c5042030005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 86357186 1250 86355936 86355943
    0xe09060402061b030f0c071a04030305091309060c02010c030c09140108040c030803010b04140f1014070c140906010809030316140a0e0102070b070305041203050f03070e0a0501090305 80
    0x20310080080c03800c0c072880200e640b6501ca5455030b50017804c0c0215010701e0401d4006454001d4440c07079542d111219241000c849402c0c000d500000340410310034400c129082c1030011002c00c00e5041c1140220f07000301c15841d414201c40030410705c100180d440d00301c44540f064140c0075040c3e481510349030200103d841c0600d1841c2a00c0312929482c100a0080007040511041943c05000746402c203880f07030356950351000300840c5a030181c40f490060300000300208450746000f0081408800002c0d0000070030310701501741141c647c13107211802010131500b44000008192441705040c0030306040c08d0980d0700d80500304200050020001d1003503040150358801c200a5000c00310903070381c00100e1003040c150304804800040e6110644d90114044044010403807895071a4041e1961660340d43c00c1e0240c6d0b400ca130316240c202c0c08d0b40c8540400a8081541040b04200c041c031081d08110b0581d009250a41c18103401000c59011503000303550100000d4202218413409150148206000f0103007403c0845605245940e4a1f45 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 86358436 1250 86357186 86357197
    0x50a050901030f02060f0a170c030c090d0212010c020601090f020702010c030c021c0807030908060907121109010e090f030910181a0a1202040303050717090612010e0906040206 77
    0xb40f4001c901d480011502c0320003c1e00e100b9044114243d449001c0060001c0010050b5150380302040c01c04404215010070740b1048038040d00c0d00c50003843c5025140820701c500e80d01c20910072600612503d4003440400b00038400c0802c3c1a40641c043c0146516201e600420345000302046a142841080300c880140e07004522040540c3c1c0c1410b0520642050b400012014100e20383d0700c0d82c52141c03840002040002400051816503c2911503201e999200d2844031b554950450380c82d60164001d2800b8003002481441c101e007034078414840007020080b030380042190b622080c0c1c0a20b5044042a0a105901030140709200b003440c0d50b000110308002c4c001001600c02c10704c040c0468103000706c00e240c6444907240c404000010302200440e40681000341558032009500c90b80001c00081c031403001c070300345a55040c002c840403640c1550314142003210580760341441d1180102500c10a81d020009247d0359200d15028008141141d21000015032601c910710505940c002d258260a802000c05c100050781c44030160f81 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 86359686 1250 86358436 86358443
    0x30a0b04061404080408150108192303030403020f0102030c090103020702040e120904230c0307050d050702030a0f05130e0604020720040b0604080607030506010c060c03090c050a05090103 82
    0x251512603003003450042400380c07460000384901000f00300c01d00c414100108120b031004411a0004820f49441516480013802001100e0304000a945840030b000b000d180d4005001d981240741045140d4048400200725005900c3c450f0400f004010034141c0600c01c0c0780c241c49508009518604e003091148545110b200752250505501180c403909544681d80b245001a20382d00854101481441000202d03800440e000c5200d02d080816059208401c0408d00340004244a0305c14070742d07211313019500442d400040c6071004002041c0013043c03516405020741c3e130044609402556030b0314641c502c02412a03d00310010810b01404008003400040703c01a50002c903000d950304050b45444401c00100a0311404001a001d62035000d044a80c40310b25050102c0b2208080f501004803005020900c00c1900a910a11160360003210000e0b880300d000342c1010364002414586004078100369034848040f6001c00507030100080d500d10f10341040160300b11140d00901012103050f50f04600e05400910036050501009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 86360936 1250 86359686 86359703
    0x7030c030b01060918110c030c0105040c080a0503190203070506010b040305060f0c0901030f110d02030105030123150d0c0303020a030801060912030c05010b120a0614060a03021c0804090606021b030a 87
    0x31b05034420240c0c00d4400803280002640da03141c102452079806840b007514150341060014000145413180010240c510b19030201c0a14106107100a503515419a0344980c01d00b54002000f5400025000344450342c0a0031070056600d448030b0450030100d01e040c00040035030b420390300c2803014040300d800d01d581130320541d1000340f0f000b064a100440c0000007030440c600716030808100100320001000030320780280d4140d6170700b0340007007050488800300c090301503000b10720310f40030701044001040c098000d040405980740c01c00342014480c0e00175a503c5003607105282d40143c1c0160403041494042650100c0701d0b0703004240d0303403510140f420b040003580c0e001c920999100400b840000c00d20502007007401c3d0001c0710307032900c0208a1211003030441c1c00151070712103880088890903d02100c1080c00c40d65041114084d5101400d410180b80c255401d111803802658000c0131071800c41c101860000d81030b140200064010000e02081d42c40c58804060320304412401440c10b080000c0c02e120103d601c001412440c03440c0c01c00c0c00d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 86362186 1250 86360936 86360951
    0x91504140709050a0c02151003081605030f0715050105030c040f0f1b12020a1704030309020306071d010c0f06051801020a0305160c02030606090c0c07030c030b01060918 74
    0x20324907100c00c642c4003482450402d41003103803480c401d500c45120552a50250341c1c042c10f8608224070a080300700d442c0c42c1910b00104042c0301242c1060090070b1301410440d0030365070034103654607480c2ca50303003222100c0aa60703a00010500100150540c204005494803081400103504120000361a08000515940500d581e0304420480551a410030840c1014030502000902c019000084c1094521510040032070000016080180c40620880b0702840455840680c5074544101e10b1040c4800900103030201501e4501c007001694017400300174040d0859403103492030301040407040760300f0350940c4244a05101d0310001d4074010803144400307502c0c69540140c0c001250f035102c190307500c23482030744c9072502100b90320201d840744030782c0e42583c00300c0d005084082ca00d00c80d03405a41c1d0704880350302607000002c1d05508668040b0703005042000c8403d42184130204203604003800c44420038602042a482990204c400701e10800034081100c41d1140940036502d0032007442410f00d410580c0d0254180c1c42c9035000c5a955a6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 86363436 1250 86362186 86362223
    0x406050603030904140601110303010b22081f110c060c030402041407080103030909051311131505090901090b0714450109030305090a0f030b0f091504 66
    0x4a50f4505002002000442094014981e0440d01100d6040c00300b0340d00d144050820100000b0384c1c0c1280d10301998180303040300350700405c000d030703021000c800004041c044008900c110b000d01c000e0000c40c160503035540101c0513508104058a40c8010818090582082240e010200204000e0b92020034002640d980c0e48851010400502000f403028076042100b00610103134950105115040324020340e1145101e580302d40505003192400d442c2e0004000da9407250780f00081d070072949228441e50080c03900c0348082003090060260303041c0d042e0541d0b0880c1070800074004c2e0314152070b0700e1b0740042c2c0034002008038551a130743d08641d08034060821301c00e00c60b440809189096007038007110365102028640400d04904128003800010110900c40310f0903648901d0005a2148004a4106898140c2d101182c00b8a142c500b650b282e07009840c004d80180340f80c3c50100316465000d504a004611411001d0058031304400e05000c40c250203003110800c2c2c1c116402c0c0040e039150544e9215046904092040c0b900f418000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 86364686 1250 86363436 86363443
    0x103240b0c07120503030a060503070b16050c0405090a15060605160606090f0c080609070801060f050702040c051c0203010302150f0d09030e100207080303070311040e01080703060b030606090406050603 88
    0x180f05100035041140e1503010410301101460143c0750804003030205940368030805844030340500072082e07600d600b8025400480b01810103840c03054010026201d08c051280b010800f5610101d61800c000e03401180c0d01003c00a4a242c584207802d4104010000700d41003810003071041c410103010b6469843c56240321407e2010650241000304000581004114114a65030300907007800050180802d28800020341c0c18106514014821422940c03081c81903801c1c204240c0320b132500070f0001d0003000070a020709401a11540b103801c001541c00c1e100c0d42d07214508030000da036030580c6e44080b0f00c42c018018401000140c0b0f424012503c01400d9400d000d444071440c104240c0e06008056041c0002e0703040000d01000d25820a1382091618002d4402d212144490201680d940310b40e40b103203590903801000000c4409101e40d20000308481d50075481880d05a07516001c02c0c141800ba0041c40c1240c02146040080082500c00e603121070105030043e10a80c50310740c00144205070000c00140a25841d08001681ca036400d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 86365936 1250 86364686 86364689
    0x180114040b04090902090106032c070e0c0301080607092709020904060b0915090a0b01090506030a0c1b050613060e03040803270913080708040608060103240b0c07 71
    0x244150300d82d950340c40c0340c0c005060054803c1c2d0140b80e0703160020076078601c00e010740c0780b0b081e426440348030080c1e181d21104200b40c0c00c1c0c03414164550095200200c0c44846a05516008248200d03e0589a50400204c0d0341000b80281440003807040d0b02c0d404021001100784c1408454103210501c11101d406200c03103d02406580000a5100070000d0801040200d01d50200085c00703c2a100f100003641c900001d14910800c2400181d8891240030000759003ca20742c0003275034111810304d07028001c2e65542000c02c04940056a046000c56150744c000600b15900c0401624100d005009a140c048065215182c440c04080d081c0582ca107206401c88083c4540c0d0341003103e0700c0d04008102d80d9603d0380d441c14581c40307030440d2240f42c00aa01007076030312448404603080460842402000c0070348548030b1032176154020031564811901c0c0b01003884400c011541c0c2401800040c142d50b12210450318041000400b21031100d030009103481030480c100043c0040d40540c400036143c0c0c54001da41d54014051100d4a80b00b5131303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 86367186 1250 86365936 86365949
    0x32a0607030f0e01050901051b010207050102030f0403020f06010b040e1503100c0306050f0307050d0512040312080604090b010b090109080d020d12020403030f032408070611010218011404 82
    0x120401015441004550b40040a90383e14030072a500000450705481065815800180c050011020030343e0710f03c0f0004d00c030015000005207800102c2d0740d5503003660011034004014588520401060540620214042c8801e440182a0315030602e02108107a0040740108034003000d0101c00074041203004071a0707050207100101103600c800c00281c0242d0243c120070844070b00007070604100146074105403041c1008010010007410b00c0070300b80820f020030b006004074184d40350b100d0310b6861002032460000800245018821074415440220406800c003100500800e000e10304d060705050100d0307058007190307055904444076541c3d1543c5c08401280c1c02401d54020070014052591080003043e000103080d440150b0549a15240e108200c0c035a404a00562002401050606071094042e0f4840c1c2d20170034101d4a10f011a80044030104010058240580c0090000d544404000d21442d6040310380803560111120003940381c0b041540890355480d51072a1040d040c404a68841c100440020061350041c010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 86368436 1250 86367186 86367199
    0x501050d0b0306010306020705370f0230010615080c040b0c0a0b160c0b060a030203071d01050102030c12090103020c030a11060c0405030a0f080c120301150c080a0e040f0c0c0c080c032a 81
    0x200dc0040224007100161221034507503000d03d807480c1c10506006da08100d80400b041d01c0320720269072000b41c1705000d0003007404500c0310b020403003c00e800500c80082d2000e280744100a040c3d0321158540b4007981c000181202d2120030001035800c0c81c260340040154401c0c0d9000c482014540c5070b000101e420400b05030030081d818028000045154450310100240e403046080025050383da890005907140d2161620304215070b0080c2c50600b044010200080c01c04c000189401803400382c004160310706681103d04143c0c00604512207404428200704a400c1d08040d41c00c1c00246400e01d0580000d54907140b8100c01005500c12220344400e200400c2d09035070700c1c04009000d5400410040aa001c181c0e03009008403200310030401d08a03e8140e10442e0540c0c1c06952102c12030385030001800040d0b03158001240b81d41d900c0340e1100740080c0010142d00540a100c00e140d00c1341440d2070014030708446000626004203100703502c4926401a140e90004201d908065618141c0410007200300e40818a0341c5604e848580000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 86369686 1250 86368436 86368459
    0x2116080d0e0307051207050706140403120302090a060509060403141014090f0109080301050409020a05060a030f050604020a05040e0405160608070f0206010f0501050d0b0306010306020705370f02 85
    0x441c0030000f00300040c45034056900d0040b0f41a28035895005101e00a8032035130022005102c0e13076026002c1d901864182d00581c50400307a880d0b9410f0481d45040400e40b0000b0340101e8844071905000590340050b2145003000ca00300040d190104066015910010f0002644c040c189030420070f0510a05020340c2524905002c41c40050000e002045025685102584941000082c40e0101846041c1849a212441c14916486c000800018202c0043d050fa44040c2440380010300388d503140f0017055003e00350f4401240154030b1007000c201301c540c010320300c1d03008070b004001a541e043c1d408802c480907074601d000c7c0e1594a0f1900c0c2891890130105250aa5085c0f1218502040307850700014044e118403206e03640c5403020314525100320f0f1201005c1c4520800329001d030506006a6002c0e80281205140140300013950304800380002c1e151150030303402945c080750700081e000b084c41020310403030b0903a44511810a50340c0d07001000d4525542e4030b03520304480d05240200950100282c0020410481303400078000c52420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 86370936 1250 86369686 86369711
    0x50904020d02071101111f0504140d030b0103240905072601030210051306050c0312010e0603010605090103030801030201031116051e0d050d0222060201020c2116080d 73
    0x22002c4d9190501040700420b0f9500000d50011392403a4006c2e20122030011401c0030031a00b00036000103002145c1041d81c14095802c08a000c1201005000039541e000c102c01043c01c00160458080031442e0581d16051603000d540e442d40d0a04c03110465107040300c000380301d40d034080c0d003100c11640205013880c448079070f90340c40c05034030034a40030b858107903402101c40126103151607800707a40502c03601000303540459020a0070841140188040c007004035110083d02d1801c108440051009002604200d00c860b078031605001583c00c091107000c001d04802e40b0031601030350464038003801840051100904264030394071052001100002603070300c3e50b0403220b220301d91004149405030b210031080340b500320711101c0030800318032910001400e980c40300c01c40d4907041d1824903041c1e05200a54441c80a407080c080308c295811000c0310034052440020140f90f400161a501c80c401c0c81d030b040454510700681043d41c014909030712703600e262040785c4180c180209855080349061602c92003034000c2001c08a50945015400540c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 86372186 1250 86370936 86370953
    0x61d030a080f2101030b0f071407060912030e25051f0e0405070f030e010204080a05070e070801051c030e060d06082a19050907050406170603030a050904020d0207 71
    0x1410f0540b0080005284180101c4420a400b480041c0c8001d103d040402c1c0b815400c0508140c00030520700c2c104500b030341c020750200c0c003d511542c0e04443c00d50740c44c013010040c4182102d000700031004510b0280000d5500f550701542e68000c4e0751601c0c1c1c1c0030b1030084025045980410348407004110141550040401004000d0f0b8440c1e818400a00802c03262028100145031600c1103611892003609c42c40c4440744c60200450092408508070f0980b503501300004512a9800c01c0415415846000202492400d0091640b801c0034081d000c00c0c188407003840140017564414002c40710015188540004100441c1002c44480b0140202181c01c2100080d84c1c942c0c641030f40c1c1146090341e200b0003c86000d92800c154050400311404502c000c07007441e11210050b00c2c900b80307813982640076100e410a039441d51100002035805406494080101e44001010403c954000340051000d52291902e400945000c0000c2512445440c4050003000000076107070240395500d80c151002c4801c0132504545590322494804070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 86373436 1250 86372186 86372197
    0x1203030b1c0b0a090221030301170607020607052a010e0c0604080309040b031227040507020a030f050c0604200603130b0703060801020309070603060f061d030a080f 72
    0x52601d00309122415160200705081c1c1690241900a140d95244405002800350b104101d900c28041c0752083c241001018803207003a2200500035565a5240a4042002c0804800c044016400c40010045140d40124881343d0103007507414029a15481000345540c24400340d08400c0100c05c0070003188015020551081013045149821034110300f24110030081140210310607020150710400c522101e46c1010703008080040405011aa00c0300700b45222090280c2000e00e0130300b0440c0315039001d003100c1c80702800000326060054804000350305040b04000d4407000700c1c071005014081d14050b04506c0700d00c100c045640200051003aa80c031800d21b490302580208950303070750329181007410400d44207034506101120302034810702c005400b1540480c0d1b201c604490b401800c02e814555580d400007000c140a0004600c035807120f40103807500e2400c00034050200c62903500068030080005905103e0b031a00f180400e02c24984280c032000b21624030a000034900702c40110014020032011030401d480700f542034003515 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 86374686 1250 86373436 86373439
    0x307060e0601080f0601050d0c1a13090e0d0804081303050a051b0102030304030c0c0506071103060c09011b0c080a0b07030e0607090302130b1504050102010b03030a271203030b 77
    0x141c059980f803100f9551982503a540741c20f1030b00000010407240c9482c903965840e0342d1040d611001090f40c0c82100c50100282200f145203420b1000400c07901d0021a00c880102074581440300304501112142480d503074000d81c0b540001400203090100e41489803100c183c0713a0760603407804208400350b100d103000390712405841000c0310107205400c0c680300d030020050180b1340c9038a4107900850139075507907803000c4a2220100a054403003139048000881c0d640c03290002440d0003400b51210f170300d0000e40d03202410f1400100030520a910031060100ca06030b41c0e40000c4e20031142c04513103840004000300d41400b28034907455034000d2440344108601e1108211050031514401d03000340e1403c202c030310071105240d51205011a0450009850580140010314062030744800f01008940d000540c135200a01040c079846010303e20080d4200081004c00aa690900400d40400010307000796040c00c0107041d003d0318820401d4224005082c400c070a44050101c60301045009140710289014584454200600100b103a5505036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 86375936 1250 86374686 86374693
    0x51f090b011404140a061d01080a030f0c0b13020f0405010f09020906040509251e0305150d0c08010c020111030a05130b04060f0c08040c031509080c030d050106110c0d0809030307060e 80
    0x1c41041c26900e00123040321404800780c001c0460729682140c440041c0c5510200b0300502c0004e410104008000a40c481c1e150088002daa00c619401081241251600014403460800d001802610f81e2000c0201c102c1c0d03030004015172034101100001d030b241c1c0038039005242c1160740b4008200e140f501c1c1c0710300c5517071031203c0c002030404010524104031400110b0707001d00300c8148049180c5d081c0651083d404164401103a444d60900c400004001964cc80c5420100342c1d5440c20780c0d0800c7c822808280300e80000c04009000030404400d0881102c2994013004040016081c1c0e00d6000440e40c1000158801c03840760f0001405059240c1450007c0080040c0940f06000d540b03080300b44e034515401a40418000d9801c004403840c100e2569031400d6400104203400d185880d00c460481e4002584e8001800303480d10086d014580300c0c109100102c0403100140d20050402c004d0701d09c1390261b058003044940e450030054500009408950030481014400c1c460615050f200c0054008244840c503404004900c5402c4140c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 86377186 1250 86375936 86375969
    0x20a050306010303050a0c060608160501090918020d020d05071d060a0303081f15022515050d02070b0c03100501030c021b03150103051f090b011404140a06 68
    0xa140c1c0e40e100901005012500401400c0305284c05221200c0300c203803013800701080454480001904022100010484064050000f1b00066802800080c007030b000b101410000e21380b00e4074800d501028030210282c025841104101c007552a0340d41402d8103e904841112850b6503a486242003a2056110950400800c40007180e41440c054440074201d84c0c140d511500c43c5e45483c4059100100450f480013106803103058005600f030507a4240480368082e80c1c0107400e8911a1031400e040362140b130142d80c065000040000c0c4041a492401e10b0032544085c50480d40300c2c00700201030380007403040400142001d100f031030801c0700810451000394130410400c204011855030303d80042d41511001d6900001680001c00c0c0e501d2484030050800301501c0c0020304580304072110340401d04801e50281c0059900e600010181400300303c0b04007180300e0940c90080700300003c031a251284022180180140a1500d001590a0100c0c1e90b880d00645100c0220601c002070900344034641d000182203d10801086810201d034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 86378436 1250 86377186 86377189
    0x6060f1a070b012102090a0e0105090a080406050c01020d09080d0b030633060a0804050607080705030a0e0c0a171b0a05060a0203120f100b07030f0e01022404020a05 72
    0x6440c00700d41d0200c01040700b6400c0c51301002014401041c8190300400d600b110714056074a450701180560b544030000100e80700c3c4503081a0946030014081d000b96031203949602c0c00543e500044404a40d403500e070154484294140f9580640715188451011a040c21450418040c41200070648e00380d80230030400c42d100c4014185034480000321100801120b0003406a41810114aa80d50b400c5420000c41082803c028002403000c2e001991410300080c0c116080208100e01088065044801c1d410302e00f0a40c0341240c030040c464813009180c0c1642548541905c0f10a0b80d0400011500c1d000c0205031429103511b9a120002d034807003080c000c0354076100d103c04800544003950b40340076020b03002410000c2140d007800284840ca600880c82941144020005400d4020341401503d005500f000c1c00702030701e42000c040159801d4135580040a81c010100001d90001ea0414440c1b981d40400703091070068a01d00c80010f0303003020142501e02c8540d203091303030410800d40104012144214400c9503a840c007941c6810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 86379686 1250 86378436 86378489
    0x21c08060d0204020c030f04030b1f0e060105090f181501050901020c091e041103010606030507020607030c02031608120c0903060a02090402090a030809011101020306010c0f02030a06060f 82
    0x260302540240c0740e040d0710310141c14160001c04100d01c1d00e0303044030328040381c105001c40f0030340c4690b005481d20f1072880c041c0825011002c141e4044074034030000301c200450401d1640d075a0410007610881c144007000502c1146501da040d062000003800600154544400c0c60b811840c4913030440c1d03403001400e18800d4600d80c0c0e41c060820b81e42d424006034000c0103d180103406110703410402400c220151601288006d020f800649860f42c800c6101d80f480301e804240d20005c1c1400c0d191035801c44820716052004100190f43d002590a0b0b103d000381c60045440000c01600340e0079803259401001c400c3d2161190760051181810003070840502d40c280181d443e640e100c000103114000c00d84940d6054114070082140000d4503005040300e00c400501c010b140081e680c00080d1500c403154400c849805010940b0841340d0380042107046e02c000140f00035441d40c03406a00080c011001800d009040015a0341001d06544081001d02c03405980300c241008520344591107903c0042045c070590381240602c070031100c065461034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 86380936 1250 86379686 86379691
    0x2090f0109080a060f020c010207080d0e03030606030604020a0903080c0309030c0a1d250801090c0801080c040207170301060810080a050601051203211f080c0f0a03060507021c08 78
    0x1071000d00031482c030f81e94640b000b030b00c1003081c220001c030703028015641040802c4c030003046154841c414441d0755070f156070350000070b0342c1403201c0e00051900184204565a02c49404680c1d00c080100c0300144d90300e141c42025503400e80140c1002e0b040340c00110b490044542c00100074041d2040032411640340003989030400a40300918054072600c00d00b0f4498800001c0d11004089805c5a03440301d81d00c2d40014418020300703400003072800810026415030010400c2c04da4601c601c03040c12040c1d252000b1650304001c0c42c96a03551814001c1d42c01a940042e0030024000007030680c4001c00101822071740c0e29699103000230100c03502641c06010610117605c001070760010014000d50320f80d1b441009855560300c0c0c0700c1007050300340002502010f0fa001c100801e07210000c001c40c400306a0340b143c804400541c244002a80c1c012980d602150007000001c0c40305201412000540d1041d034042102d0901c8403c00f04404124542ca05a100510682c188024040c4035030700850f10b82210301200341001c04201088030212a00c0c14103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 86382186 1250 86380936 86380949
    0x3060b040e210702010215090607030605010c02010c0b0a06120501020703030509150426070c0602060606040614090a0503060f160e09040201080402010203191805010503040314030a060b04060302090f0109 89
    0x103980388000402e030340360040c01000c0d005006888411001d0210000d20610842d0014000e4104100700a0055054403a8001038082842e117102c000710b0607400a01811820800030700074217580400a0704103a210740240c40500155184040345215902e13059000c0e401c15201103021070b0809000176001c06c00000c0000c11400b000400c140e003a00c1c2e0f901c80300c4078082407420108103030103450232400d0502d04000080045d00d01c02c1c04d9030320903240341030030080c1840409041d86120300020841000125400419040c2c0c0101518800348e55411060000d0b0181c07001e5408030313405000d20010081000c1404103014415079412403007464081c14444201e0300345080c2d02401d507204440303802140c0554414031015030b0191041c01100d1502c00000c650b030459400113004540001c04004101e038100d00305103c4000182000c1c2082825801d0665020b01520380c66281e01c200d035072012001410742c107000e8010000400c445801103a071140c4412005000e9848480d0395070054040c0b0411a102e548200b445030b045941 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 86383436 1250 86382186 86382223
    0x60403090b09010e0d1407060e0a03060509010e12041d0408180409050304080d021204140904060612032a110d060b04060e0702061501050a0e0d0c03060b040e 69
    0x8051110400e40c02060b500c41c100003000708250000d80310360088004550141ca07415071000f2402e0840c5180c698036812210410904484403c855241d1032101e2040d65880000890740c0ea940d184114010f000300c01b41346440d0320858040d500950a060020005e4403200700004000e28814958030300f0004050f18010f0661b0401c100c13280041d000d900346458030f858000c00111380080c0c56291285075070010781040d2481d80148445404541d010042d00d60b4004c04100315a0510b898031140b1242811804550340c00380d40c401740001c0030010b4550044015088000f074400d0710030302e1801e0050001900540302014280c0e001445d6003151001103901e446280d00c4008184903409400910080f40820740086032459100c1e82151015501c9008041c0640310300700c011412407809040003490043c010384070b108010a428003400550741c1c810202d81c068145130804402c48514480403d000302289400507280a006120110400100360821002440100e50500c943e060f202c003102c5d25850301d42d41c41c0303d2590 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 86384686 1250 86383436 86383439
    0xf0807050909012c010b0f0307030605070c080a08010e090c0d02010f0504030f050c0415060807050307051209010902100201021602090604020f0a11100b1003052205030c060906040309 80
    0x1500c1d07121240e00010080022601000200c1c513a0311051000e148900303000c0001802020b540c0091007811a5990115126a1501201400b0036107034801e6010280485844100294885000d81d40380e002165115200035070f03c09002f032008120800078020741581544440104101d824001400150007600a00030516003900b0341c010340c0c43e501000322020910006000c00400f00d04102c40107044c00d4004d01c0901200104881081308980c5254000d001c80950913a0030711070141d000c41d0b442d6008506040039592912411001c0e5002d00804500d40782c104030000030009611019000528511320940321600b082010758416401e074020b0780820000170340916050b138054602004140d4000002400040c900890003003654840e90024080c0f03404074072340ca901c204d0341d194200303c1414144070200d401c0104503855000101800000e410400801d500c0c0c3c004284d01c048415007280c040c6c00e400c10310810201e0710307240c544d0700ea8000d102c00c18120300503580001c035140300114155100d103078950344127003806 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 86385936 1250 86384686 86384689
    0x1020303190e010f1b0c080703030b030307020a23030d0e0d110306090303040b0a060b16060e07060f0909060503070b070f020a03030c0605060102010908030a090201030b030a06150f080705 82
    0x40d9040030719086454202000c0c05440038400c4200740200c9000218140091100700f010400e44201d0103410040780640c4100402e0b41c450070388800359498607011880ea002100044e266004148019500c0b00c4403100000b0401a000e0049145903c1c180b0490403c02c43c2004041e01c0e08500151400414170030b040c144c90744d20340b01802303d407a82d00c5407140b90080c440b1a00401e15048049a0680080e0310010134403082c4021022160341c880e80c400745c1400080d0034907411000c0c50003030441450310120520540000c100c0181c001a80340c044540c101c9043d04c0e41d5450041c0b01001054062002c44c940c0d0703801144490107405800d040e604041d0042c81001e00e000310907007160348480303030640f2403002c681c42c081c0c0113a907448240f10045000c2c1c0e0f0703400548802030621600f03c0c3e1010f40243d043d603240640003400154000241c030b501c4560b8510001d245d0b00740e400141c020f025900c8180382c0c0350040b41d03220000c010403540701c4000c03071080d441e0640466844032605a0308043c14001d02c00a9445480e040009 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 86387186 1250 86385936 86385961
    0xf05041b0816120c0206010503070f0f0501030f0e011401050f040501051507020d0501021216020f1218060715180510050c0f030403030f0f090b010b0c01060e040510050f0601020303 79
    0x10b102031894180814850702030310104030341a80c120100180c11140c0104054602000518003030443c90660403003039840c1140c1c0c02c60806007441114141515a6404080b25049610004011054200900c0107071208103401041400c02d000391440342050105504550900b441400d040e24409840d19501c548039190710b18564110110481c1d20211a1031034100003402030003d002486529210503c05041401d03005c00610880000742d42154030030181da000d880000512503010400b000490750355442d58a0300c44a2100e80f01c0d2080e40c0045000601c1810003400b0228460400c003500020094541c000000811001c0243c401419a900031103a401441c1000e500c92030700b00f6021103c0620b40840002e4040c0c181d002107170f0075800300c0e58840760081c0b0991030740501004000600f0040059400654408050450600030383c1c002c02c8003c55005070080007544820098a107600c81c41f002840c080c607080b566009164a005481c50030080414044014201c2c200d0090740d0580145040d070b034480c81c00030b02c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 86388436 1250 86387186 86387221
    0x9140901090b191418040302191506060909050105090708041104090b010b0c0105090106052103040915170607080609060a03021009030317010302030304050909010f060f05041b08 78
    0x503c9110144902400c100c4480c3c508020000d150700801c162454a0030801c9444491a6004002a003801040300090380440c808800100581c9101c02a040b01c0c14035410000c2440314031071138140792400211701700e17411502740c004031070a0305020301079a0b0302d030307401e12032000380c142c9041d00070a00359404038000912500490710480400b810010309407a5541750342d240e041e000e074011203000d42c1c00140c0c51030001c800c1c014035501046200080c0300007440c00c00420f0404910303405104188140c035001c2c4242c0310003031040324010005040180941c0b004d43e0244100d4604030b20070742c00044070020900450a00100b40940b003000240c0320311106903155028400f50801c002c11065009503c1c800100040e601c015000e1141111592000003840c03d40c6009081400c030358881c00c0d0780030241c0380104010f940020403a0203984013500e9036240341d2500201a400740c03005180e000e00300c0c3e090180100304da00b4070f6000e540407200201ca081c0000b160f031254025108141d520181c1c00910203000140ca9000312004001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 86389686 1250 86388436 86388439
    0x105030403030207021e0111070614130f090c0909060b040603020c0a060606030203070909090506042d080703091d0414120c1b010f1218080a020109020109140901090b 73
    0x1407816075185c3c0000c010382c58008800c40e040c9442c03046c2142c43d580c0464000c4215042c0310017070100c0d60501d2000340c5084400112046048070004456600c14031501c12140144050540b15021544a1000300c0140900d410440005484e0038000200340995000b603908030740d02180300c18582401c00c1000c07006076010420341c1c6400e1140740110000a00d06228000007008266001602c81c2040c1e000180007034580da121081d403d060030344c0c0b0300201d08003151007508564041503c0d9000c9400b81030100110000610b490104602d654502c4140040c060041282c54401d903170341c1b8000c0e80c4810840c0300c0141406401401100481c1c0080c0004902c0c41116040e000c5210442c0c990066851740c070002980440e043c46100c0d00504c85111540c854919a42680202402c040c1c00b038007080000100f941c00d00c0101e001c28203460318250450007400038061030500c0c0c4c00c07602c100d907200c0d05104042e02030b085140c001c90000c0c0c070803500066000458070f42c2d1801c011005100c030b400383c2d01e80003074107014012201c41d00c3d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 86390936 1250 86389686 86389691
    0x50f2101090308060d2612160801081501050402132309070809061906091812030203041205031e01060203120a0204050616050111120906070507080412030c0b01171b010806010503040303 81
    0x119050400b0140c5520514254501d054112188c0200030144541039008002030b03070000c003140800c0003002078a81e0542c0c10580c4e0050b1180e0005608800b00c40956200d0b40140c81042c594100080701100041c14a5070192a1302c1115298403a04546042c4200c4050b42960000000304a200c902c650154030f801401e403602140c2a030b1118a241c0c02c8808000b885082c803882c90300a201040045000000d0b0b2811605086082d0f2405483d80000d81c004442c9680c10000c0000011b001400c10349411110250304200b00039696031a850080e65076030018150b4080e00b070341980082d583c810309000325400d03a00c0203800c03a400e114070132500032040c4618403c110303a69500c44580840c0104041c018003000c0c030352201200c1d000d04003840080c0c14014080c11450130801c080202602054101c4200e404845082901d280588114102100e480c444031000400780c90a5500000c0d03006007488c4200f444009501c10b0310180800d0003100d140510b01c404400313000c50030301030000d403030780d8014405583c2c824080e0501 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 86392186 1250 86390936 86390947
    0x130203070e090705030f0102130b0304080f0f030a0506030109030509040f06170c120a030e060c010207050d0201061a1905030603071205060709091401050f2101090308060d26 76
    0x981c40340e0502101d207012264080d00c810800f5103010801d2600c0c25082c44000c5160009917109001c1e01c983e1070180004086c000000300e0308100da0074045030224441107000c580c0b6005007409080c4203601c15205030851038107260106100b450b0610940c080c007503150711111f1400182c00e00307100182035a0901d40d00d01aa95003400127071604030f442d0600c0345000c210003403c06040300d01c040241c074044884605115620180074840001d80100b030411840f001120b50a446d03030500e50245019100d00400103105000b0b00c00b03001605501500a070060381d0241070240741201628004030f080d4001d1502c442142d00f84184a0340c9454080c034001d60b00700c600901542c2e487c5480f450200010369003102c1c200c9803940000d080045503584803405034040c0c01281018007040850054a58a45006000341d03842100e150410030304580c0c0d000107a01c080e144000c180c91801d1b2510300118003e01c1202400c0d00415424000240c0c9441d0415024a403558000c206d804000980041e00d031352501c42030075002080404000c0e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 86393436 1250 86392186 86392199
    0x3020c0118020103061e051e041503050f12070605150312040303080a1a0f030120190203191805090a0f06050102010e03040e0c09061b010c0f0813020307 67
    0x10350260681c05012112015809100040c12a54180d105030003100f800e004a030a40c0c1200c262040803141c003100c0c03e05c00c0c4600d1740c2c0c42c0e41101e030800031060344c80740c078003858450313456000c0e070300c203c212409a03094450791041440c025482d0b2001d0044010000750800c20140010b05a901103a0440c0803002100702c07a6a594000c28a440404200c4401d001d10210b070400406500c000c070a03601c00444682030260040c00030008081500094410384039035898100d142c9940c034254009948085c110741100c5007182c20100f041016400612a50010360107030002c8411103000000310740b4030b41010940c0d4080b00400c81001c4800180d07005032a0840240e140d130005a6544016100e070003160032660000d20007070144500001c076040e40c1d005506690501e20203038150140401980c086a90341100200d8550703498031140c0c900e01c00c085c0078951092000c14415070074959000303910b0030384400000802040106040585100e08106100c000082c0000001803124041014600703045102504440f02281c8400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 86394686 1250 86393436 86393441
    0x2070b03090c04142401090302272406070206040b0f0408010f0c1e1413050409050a0215070f0809011205042603090c0108100306021207030e010c02060a0c03020c01 72
    0x502c40e0185020140038010100f4030b171004e040385c21407540c2c840c1042c0700c0c040001030405d943c0e0b444040c1c40f513a1008101501d991155000c0c000612800b181d04045261601e2142e80411200100c0c00c1c030000280c509280c107041090880c0c1c40240c0041079603007014607003a151111a4042225406080700078000001c951001740100c2201c2e8200d0800841d04a404020041c038103104400c484005200c4030a0015a081c0c01c20a0410b401100714001130b0741d102c1d0304011000030241c41e801980c02c98a401480d406000c400b146c00503c06101301c0d07403131285c440d9000300303a0428001c0b40d2010303041d958034941000004940d20020044400181084d1059145d0802c43d17404984084505942103185600340244c1d245000c00c4504035110122119811030809005d281d07900c0030800501030500c0304410100340541e01e0342c1c0e04c82d80110391058041d503a450b000f090401244100b0713211800441d081107955689010180601c809640c01035000304202e607150302512000c3d040c0713189460b062541c20042c00d40d40302401e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 86395936 1250 86394686 86394701
    0xe062d04060603020f031c030203100803030108010e120f0d05040317040c0312020f0a0b10050a0303030606180501080a0903030b130506031b010c0b07050d06180b0108010602070b03090c04 82
    0x41c940040c0d824918014030032801e0000007110304c26048a400004a07004030300b15130395900070520300140c907541e07002c00b681c0d4a02c2154209030482c0c40301000000c0c1c4a801508640741c04180c240c203441d1030701d44243c403000700c40c000e115080041740d1052001980c510b51540c402948640030f803511641c1b00403069101c05003081e00703480a8550350401c007018810300140c01c1d01000c0040041c4010511200790b002d1031501c401410710001e04e0b0054040209a00c20300b800c056502034000142a12141c5540389000303001494288598004a00c49844c031403202501d0100741403c07034606844000302980c1300c10302c2c10001c100b80c010807010305680341c546030000d4440040d01c481100413030400203042c0c100a4105071801d80d0820b80241c0b88404007280000d42e0b41d20100720b40d401743e8440c4131390041c1c0d15024070548440c0035810340e801001d03103080030000b150b4404a00d03160142102007820850915100f00464008400f40a0500507a01881042155001010003554803280c0107003900c03042d41e137000005081c1c565a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 86397186 1250 86395936 86395943
    0xa0804260702030706180504020706020705010c02030c191212110a0504031502041203050c0a0503120708060405010b0f090d1a0103031b02010e0409020105090405040c080d02010e062d04 81
    0x1040d07910441c101080b680001c1c11050034a40e030001c01c2000460100c0700705000f514083ca4004c140c100401c8056016944c06a50040092101030094007009640703400049810805210ba0304501300780d14202e003440648030380c0103d801c0c0d8503070750b5102e0150340100b0010000440682d9803038112400701d107008041d054480b01d1344d9910381e9461031801d12046240b0120a143c1040d881000104810703144058101c0c280c03a45403d00c2c985880581c03c00030b041c0022040d015065000c0014007081d070044a1804502c80c10080e129048107480395820320088403401d000b03003000c00c0820462007040109400241641070001880407070400007540e21540c407082c8000c00c0c8104010100014010035400055810700ca0710241a01503200c8075a0700000c2282002c1c0d40c596000f5941c4ad514441964854011500c1c5124050030a00080c102480d0800368100f03030f423180d502d1600800c000c1c0d201a41c4103004050001808200406154842038205d01a944481c449140e641d02c10700041c115003c0709140e240e01c110300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 86398436 1250 86397186 86397263
    0x306020309060f040f230a14010b040612170717030712020306010804061e0213050906060c0d030c03020c0d021f09170307020102040e01090501091515030f020d060306020910020706050a0804 83
    0x12340245503800c0d147d60303c52591103242844424483c0390440040b0318070580d0802c1030381d150078002c03060b085046d208e48800642003490341c15440f403850780740344011030040aaa558503541303070305280c201008900080d030700540001c58140102e80410034980141604900c862441e4042d0007003450b07900102e030b1081e42d504290044481c0c0c02c0010b4684032000b6070f80010280c54051800100010f02500d820120b103105060641d1f03400c10188252090303060b86e4200070900102d545004107070368081c1d13031a40b03503004140c003404031410fa0842c81c0500b03006802e049680301c0311000c2d804148105101050300001d01e4641150b41c240000a0780500c0e0040c030b44d00070b003031089001481d035040c01108400d0380c0800200c402c0c0100c034103408101c0000c4881d40d25902c000c9503e00000c40010844080010b4800d10311021a02410441c01006018443c1d00406e03a60700200c8481500c8840048240c0e03c54074988107403004280c05000060403240503802203603006100301d24008200031024407a036180d681100008071a00c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 86399686 1250 86398436 86398463
    0x204050c0d020a030f0c0806130c0c02060d09050706050c0a11030a0b010e041104140105060a020709050a150e0c071218060507030315180209060906040306020309060f040f230a 77
    0x17031900c10004500611b2038011114904840801c0b10b060503c0f507026560307a0b5a13480035401034815804030705480d03030041017582c1d21a40000103802a04002009803024003403048002580c501030021103070716180c10f1001d0175500d03016441303038a2045806031000d0f4050190301a440d0002d05038018080c040c02d02c4405e40041418281271820040b18420140e50043c3d141480514911109030354090460ba421904e40d551500489012803c0407110750158180d68107044c140a0045120703000740b41d80c0e02d10700a01c64038003036640010f1551a0419522603298481c2004564081030f41d140c04408160301c2401c0596a1014048444801d241c0c50b0f07000500060012606004144d810301540203101c440b0001c504400c0c0c1071800440598001c00345010150764006104815921484150fa5101c00000c10158a4603541c1c141080a980b0031200800c0c603001e214001a0414401001140110b80101d401020b213842c0d95210078442c10900344c04a03a440c11004d160b0f2048404215405240c3e200c7c5d5141c0c040d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 86400936 1250 86399686 86399711
    0x2071e0902071a0144010516030b0402094903110a0203060708090a060e030301030501060e040f030c0204111801030501090c0813030302040b030108070e0106090605070204050c0d020a03 81
    0x382c0040e048141c0c1c2c5619030f05502600c00c80320301013010401180c170b05c42c40016024180581107a0203551481d4165081c2070812040c105840090301000006440610000d0b00c1d00c1d040204900c1020403003684501218092280100f04190301d20380c8101a001600c541c2910120208542c03d42600c144010403444242c0707070800d51301c0704250006c406510003c2050301d00c2580000d442d994010038601c1008603510003d184220100020b2003019048941000f80e10a110805074603035100340401e0b949076003880c800040030a1080b04003803103039401401d810f001d0492690200c40110340c01100ba130f409a00c070321002404658000040a9500c0100b2812059401c114009029a0b005034072003c0128548040b955002d40c000d04034551004070300e071000390500c3c82854294001e0199400414201c000400007042030080000d1110940e0084c4500ca8041d0381d8641040300c124101e40100320010348240b11410042c10b05410054015050a08a03414803107921194001c07604540b400070002500c2c1c04c10310f0f122 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 86402186 1250 86400936 86400983
    0x100207020109120b04060e0c040e011a030604030f051606050a020901030e07050f0613090e0303181609020a031b0513150509120f0601060503240102071e090207 70
    0x6143c0b82903600b00280381074031480351200004101800041e110302445190036000c0c040d000f2030040040040110401840c60742e070003080024400c041c803804100c0382959071728002030390612031079140ea601c0ca0300280340c407002c4610f50480b017044e100c0e40125410007030000d4268011140308080841d40140c42c0c1c03050308001000da4202145504141d00101000e226988500040f4060004180d80c45075454a003001c401804808540c05041020710704800400e0796140800154028007900c00340c50300102000c090705450707030002d0303201003000ba000003420800e480c0282c001c1c1800d5030180c140084c030400c10000468070b0f90b03032602c14800001c5d0300090f5240640c44110307818020701041c1046411034000b8041c0030341644500c01840e48a094114119101c92030100b00c0003a0250301001940e104e0b59503564050034a81080d29003554000c0404007521500c4003090749540407420580c001e00c4403d10341400c008089011001c10211352b2038000c004100c0000500051a9042c80340c89826990950850103a51 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 86403436 1250 86402186 86402189
    0x1e120314100303020303130c03120801080d03020c0615042009100e090106030e0a080c0a03030f050f0a1e021b0c0307031a060406080a0b01030605060609180c0705100207020109 77
    0x801e801076a6051010950020135264401500600d0220419107410f04041404080d0700040c8a80742c5c841c505031f0b0381907228020034106c0d039451046400c40704000409405901031904d0b0742440b9401480080c80707040d002e454814500c50090720000308107803150f60750582c2102c60082c0d074031103010010b5010924180301c1a10009c942503483e05c20066000100060340c1e40340b06228000c00c064455a41c0200424140107040109600c0b81d4090754a400c0102c0846c0c13a000d00071020703804030740b134406650001c8140c1d0040c6881000c2400981d03280c2c0d0750b80712200004044104035a0704120441c030b0030250004643c80100400c01500341c6203060300520444d428034020320782c01001c0c040d4001d4042040000e0016081c0c66801543c00811011661808003243c010030300c90b03118812620400c1c12134001d2052100c405810303240101c009010a5440c0c5060100c1c031301c2900c4215800c8031510321b15000c021a0300021640040c8031080451411100740c80c2c03685020215070020070043d42c001034142c1150381041c0d0000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 86404686 1250 86403436 86403451
    0x30e101d01030204080712050c03030307030501050103060b0c03090d06150e0402031c1b08090907080405100e19060b0918010606020d0e0103020c1f060317030907031e120314 76
    0x41c6401c0c05d0005254480f0003034811b4103c051001c036115000c004082c07286088c2c4a1018007125242c0c030744820020301404084c411503004c00d14041c0c1c0818091811701c02c842404030380100642c9401d521500344420401035050540d2402d80d01c1911903400380c0312240c400c0060024000650203824036004041c1040c44c1c022018450b10030195080c1c0499802201d500714070740306012071107452280d6003000d1901c4d11503414510307401000c180800c040e294000142a00481c0510115490040911082c10484881c01e01444407076122101c007130101c02c01948406c0c01941b19260114003081c82202282c0560402e49550714200829185210751040c00d10420340108810700c000c00314040c1401d4050000641014072504240d000101240142000c00054201d4040308a00c0c0c1844403804a150000304442e01086448101000030f0020100320721017540d024907c00340140005914541d03820145180c00d040d20105c50031400361030804583c10128142280f49551008034511964034844c1307074608c1d002070008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 86405936 1250 86404686 86404691
    0x13060b0a1d01020a020607080c01020d0c110606090a09020a08011419060308090904110d080901030b0d08040e040f150b0907020a151806020403050a020102071a030a09030e101d0103 79
    0x150516a8000b03481c1a40ca6015105a940c3c0c40175401c01031000d105903484c042707883d8000503901d180c3c81c00c0ca03030100440b5419175541d50210f442021890391903400036120594000c2d48800404c000e0b4205a004080d0540700034241c8401903541c186150a664404400c665070850324020066103101101034003601c5200070208114090031a0755403d058014080c8643c000e401110000701040000c4420562401c0b005000107584d04807407a084441c0c0c5c2c0301c03441560000e4100b0581c05058204000708000f00744e4041e00c1c450a050a00c074a02c292060010810354641462603041d00c0030a449404014080702d604402007455003100f0140407541c2c10142040c2c3c1190b001012890100c2c411280c1c1661055030f40f800030a480ca059600300a000c0001000030305160310018000003000b00010305145070a200781c00340c409140d0755104840a0000740e40c1d03c404d00340400c10000703050644940c032112042d40709043c00070f910343d100d80200300141204541200418044515940f4141c109082599002c0017460207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 86407186 1250 86405936 86405987
    0x160e07050a030b012604060c050a090306090302070e0f01031a06030307062406021c020f0d1101090f0f060b2d0f030a080a08010504020906041413060b0a 67
    0x14680d1003640700450805580c1c050101d07079680725038104410700d00c841e00703000041a030041011940e118140c40072566a890302c1c2c00301c2c2a2074000c2054807030383c808a0f11444282451502e84070064900c01b41d0031400c502401401107007501803050b805010708040884a5425030461070003e01084054000344d045000880c100440c41d58000100c2e01c14070340c0848003007404421801c050840388403805a03a00300701070390b940200c0c0d1564001004002d211085211040c1c03c404401e05136103401c0ea200342c200c0c81f50000110b03011902d000d10701c01c006a29502000042c140742544840301d100303079002021542c2d40041091042800814050700d020107600311008003104460309051136140b044c0c8a4031b0134003d0b00c05101c3d40c0d05903036010781710301d0302d154080c0a44000c0302017894941d50990102c90404081090500042000d08181c42601e40d20b001c00337417006291504004003140c0d0303d1202145554881074008146440d1070306c50113071000400d50403030712070b841d1146040b0103070408060103040607012400080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 86408436 1250 86407186 86407201
    0x501030f0305090a03060e0a05060a060e040f08090405040303140a1104051e130e0d020f1b060903071701180507060503040f050a050a11030f0606040e100905160e 71
    0x86500c1001e038582001c60b620500c06010030b09502c0f980e400501414070b440200311401901041244140b8490f4042c0c983c00d0780c509a43c0302c215021401541c2c01c1012507400200080c20046803c3c181034001d1450074107040c50381002030292a400c072022000245c650780403008030000342425036040b84c2c41000900c1290694003011100740120321031139100e14144906503006452041500c91042c0e006042035500340100c002034400303000440b5100d56148218814444003038804035214159030455406030803803d012010460079588682070380c80d0701071010441020266002c0000100821303480503084402c100b20a481400c4807109150148a0b607400111140002c10200303295041e59a1404d209880751070702d0400500009481e40006d120b8800e00c81400c0c24407400044250035281310f000c00b41101725480c0305154076030250011844255028070045005d901d004d4101d155014249011103c81c07501e80134544040d140c00e0340055450b0780111201d1003010000f8420a0082e103603400c05038146040001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 86409686 1250 86408436 86408453
    0xd0c150e0a0602090a0503030f04051005180402180d0302010f06080a020a090e0705060d090c060c05150606090d030905091501080a05130c0303050d0f0b15030912131503050103 77
    0x1c402402c469000505a060355210f409010141c00044d04503030302c2d00c0781c1c00f04e00a0a540700e030140900c41d018510003401850b100d41c0031603402d00b242c0c40e80d1210001a0b2824440a500081d0905059002d06807018469031075050400e003403540242d0011411707600c9084010300702d9040f500a49080d810840710000541c58580e44c0e04202c40b060080050b003100800c10403400d10045070080c030b9002c0c00c00900401e00610301e0700488003943c000c1c500761400a42d14401607440782203c600080c115002611030790a40c001000c8100e81c0301e0b2010340840d240040150001c0d00b00100f088040300800c12a5200b40702d9402c106050950281d040d41a41d40c0d04042000007030f00300704008054030344840e100c1c2d0010b4403180300c0000071681c0b983e016000180464480c5009044c40e00000142d144a500c0c2021a6810791503a000340d0b03c2c2c104010748140c03020246041d40b0b1203194802481c0301c42d1032240b02401c40c242401080244158110744c0801540d45040c000110172200c00b25904074100360802005201148414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 86410936 1250 86409686 86409703
    0x30f1b050406061b080f03011203141206040903090801110c070509060d1b0308070c030204231b070b0106090e0f0705041202040e060118060504050c04060507080c0d0c150e 75
    0x13400001c49681510f4501140d208025811134414004800021804812092040b05900c261281080e900b9145030801b403601943d8a906200090311020070120b041c95801445142e00030f24103200115211585c060964120502c6d0142000c0300203400035a00700c0a00c1040c1c081d000850b50b0a00d6814031000007401c03400a080058001d00394401c45030b11401c61a1040001190320200c0c1c15110301d180e0400176000310043c88164003c1e42022546402d0211020141c0007540141060f41410380b03503242c090098561411440d116080208030010102d01000302003402420300740d07201c010281c1003001c0a44801d4020300500c42c00d00540041c400c04580003003d45013610466500a02c01c0780060000402070502ca160711a03850003018004600c01d0001d905101070b2000c40c02c01480b48569a005110481d0011074045002034808c2c0424865184101e008200301401380c503c84d4203100b24407540e00d090045a88514000c1400c3c280741400704040100102140619100c04009024508282c10703103a440a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 86412186 1250 86410936 86410967
    0x1403010902031005101203080f010e0907030b06010c0807051b060f04061404090207060c020111090307030b0a0b09130b06060304020919150f0f090c090e0907030f1b05040606 76
    0x2a01c0015200c0020031460170000c241201c01e030714604089040c040c0140c40141c5216501141c0320002042c07000e90a41a68001c10100f001446210300d10b8844a0b527413000a45118108040029a98045603100015050070f60107540076111002d6000807001301c02c1d0711403401c45d0140500b84818140841d2440907a8100c17121420400c152500000300044d0b588150340081030424404510002400040da2040740040440c0d0003c009185a046465a003030003444001035141e4084bc0307040c00060001d02206402c10100440819411050800903120030402c441d032440032801d4100000030702c0304103c1442c1c0c00204c2900c00600d5414560085242240024520504101d80281050410790b0391b0b40074030880070a047c182c030703042a00da184216070789165210300b880319000d40c98081862500c912502c00e41d012644c0f0343c0c2d00b86c0d51912090f82000f0000428942c124013071141e00001180140c1c800b501112b10603007201c110103590105c403050015507504030038056131071f100c03040c0495074021480604c003080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 86413436 1250 86412186 86412191
    0x209011202040f0f020306090c04050a0330050711010512060d021203030a0902010e03120901080a0902031014100312050c03090d080a02060c0c0c0607060b180114030109020310 77
    0xd103002040260080200845440b03242c4000d0034201c0703034640e01560040e03004460b066010303114034040401c40c0c083d03800383c0c039440b06d8681030800000c0d4019295004800030001091542d03c030100024002041c04070044c0049800011a0004c018916810398014803003402e083d030a19400895141e000d05004120382d0041e08510354010a668605020304d50101094003169030303d02d011140c0c40c001d08443d050480c089401c90410030400d10300464814071a0340700b001703420700b0144803030011900480090003210304142c0d03404c0c440300580c600307004502451012960200f01061900d81c50014502c0060002800e035628400600010b12862075503507600440b8500031380c641ca003001035581188188203c0d503900400041c0c3d000d041200340300203031186107606d4080d82c103030340d968042c0228070380b01d540308000c0d4a130040e0081c820203280c260080e2078000d0107120001141166803010a8040c1041c8850007036042c0610010045643c206404413026042580240b22089272a40480c2c0c8d903c035900c44003440682c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 86414686 1250 86413436 86413469
    0x20601080c060a0c020d08130603020c0c150d090b15030f07031b050402120f0c07030c0201120e1029060906091c0f0b16020d030f24080705030a020901 66
    0x784900b40301300f14660020519040f031426403400e04034030b601c451503004440080300c1300014000d00074803d49421030407580103000f0450300b0300f041260744044508440c0001d03009218402040c1c24610814074120310a46070705420b802c050100078800244d0060b4a0710a620060200d60054404104141103e41c0500f07400c1d00400103032002d0740a140c032908110303045480403e1249560800004881c01115906003035200c50319030080c070540f280300707210340a03000c500caa481000065109402a003d6400c0c06c3c0c9000078030181260f0542d044c404c0f25045201003e88030400f45003030b1b2142e04089040411110a1480312040d00e50201d110340c01408880c40c802c038000b0982d1240c0340c4600034044c0c04001c10302c160289800d01840c101c0c08000002805984071401940050b079400e00c03c07074018181000304d4008004803010403104501504070700540c01e803010b4641c3d80d4030542652044d04200540b00000007111140c0c144035a6510700107096100c148298042010b08026844030381015042d651208000140131 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 86415936 1250 86414686 86414707
    0xc080f0112330501140d05030418020f0408010c0e1020030d05040b0a0605060a090915050901060f180f050607030215040803090d030506010503060d0615080319020601080c06 76
    0x1011600d0004405541c42c0107822181da03155400075060b510300d5103030b01e00b43c031100340b05011a11807001c1c40107025500c01c00051000d922551707202240040c1d211409850701e6035850200340a60095485560260b44450b446481a60001242d4008840070b40b80c81107101000d941c0281340703415130060154511030070001002d81c102c0900c1180d0301101c240e0700c14403040c14103190901c1001d104440401810b4078014011030b0038604002103c00c80405540d0340d08465082001460003480d60290758140068601c070300261a844d10b03241c40707000705042c0d20781c1800e01102101c0a00042d080407205070382c50310f10050a00102c80a08424010360700141c40d0030752201402e2178107902d45680c80ca08511214066001c020030004110015841803484406461080e20104000e405485050720010301040302400051100e04040f038600003120302410000c1b4450081c214580b08540e0b040d000300785a0303080090300c00e0000090900b02c44040080e880104125031600e240c0c1c2d40c66260042e54944600310004140b41003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 86417186 1250 86415936 86415983
    0x15050c03011202060903030a0f090b07020f0f060c0a0c170f0a030e030f1006060905030f070920030a0b0405011a0d02030a020921010b010c1a040302030412060c080f0112 74
    0x151001900f160b03038238401c108014242c00c60410241000801408002c1055407602c400d5585250b406400700003484d648100700a0501506403042d40c00010074480300c1424030b010042e890440e030150f03108090090801c0304a010b040e00440f02928550700170407544000350342c0020462501901442d100600b0718036000000d0400c18a40c01d1181d45114000c184640380c1c031564441e00848036280c444915a5990745d05250711107040c54110000c3e508110070400820520741c00004001ea0b0001180f400d19071030000d225120b400a403041448160303141075000403070411340720340c501509048049584100403030940342440c0c402d2a01c3d042081d60040301142c2070385641c3e010b542c0708035002000c0713103c552420390010b680c0c066100300b0950380350b0038000c840b00307194000c213080320b11310b500300e140c040b10484c0034041071a5550000c2c008400311300c410800014240c01d0a69000401c6109900104a481031480c00800c00d1f000900501e00301001140100050884074480c044c200ba4044000c1d100140505132000c007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 86418436 1250 86417186 86417197
    0x2e020c2205150a0303030b1309050607030905030c03041404060504020705030703030c030f051303031a030304091a06120901050a050105091306060e0c04170a110d050a15020715050c0301120206 84
    0x2004040f186004c810560160060507810800740c8440000307003d02010701043d07074100ea0024260b03810020101d05101d1003074000d94040c80c001d0f02241d00d0440740307501d640d1955000354054407980e4000b0306007280600e030601960004210845003541021401e44416803240b05100009041c10f955807030485060b80203030001c05444941d801d081100c3d20384104504016680d450040b40064501543d42480790f6446910300d00700e0802030300075424142405005802092180c8464101c15100d01100990b40d42e14030040290044022036100740c2d0074002d1a050945e00301a001680581c01c100041c02951500f201c056440240f51540c1c07039a604041c00d011000b05214bc1004801044180403c0610120300d4028000c481105a01e6250030351145e4050740c80d00e401880040a226000c44410a0b500c0c1c004011208640100242c40e4665030550f142e081c00d09016401c10590317500850038a081c01403280404511011100b4107028a18280e4100e08803484140140030070186e2940c4100299121600cc2c0c44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 86419686 1250 86418436 86418439
    0xf1b0501090308010306050601020d0e240c03130602030a020a0204050c120a1506020609030f1b030a0e1030020f0c070e0907030b010308092e020c220515 67
    0x1c074008180c20010b100380801d004c25241c080c1008045180c0d544000395101e240705c1070baa00c240611601104200c0d07041607000b00c0c814a4211a01c109083d20742400044c0780c0c1c1d1400100455482500c0080244040c400d80d00c1401950424404040140c0d0085540304802d81e049030005903556a1a041c440240642d0b07003155040c0b410b40040026248640e408200190002003c00c9840e030f64901e4200c2e0b5458085445d94503582040c0007004008608601800903c1104851604440114581c1d103295400584141c03000801200c901d0106040ca40f031024810b05851402254080007420760b80001c1a465808c610030326489465841d0900031641994640607402803900da5510744175040d40e81e41d007524003a10880c01602e00114092400000b03402d0203c03a4004801c0c04c1300d81c07035510b40700c1c002c0c1c2102403402d400408103440d119828813000710b04000031514030700301c0c00000042d46009180c254000705041c098008410403441c0d240850b001c00500800000001c251903943c091800f141d02030038903c07036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 86420936 1250 86419686 86419691
    0x50603100e10060305010915030605060f09040f0210050c060624040608040b060a03051009020301110307020327010c0602030a0209040204080304030b090118020906150d1406030106060f1b0501 84
    0x1142d1924645082c200c860583d424001030b41ca5100200484000301200b4501d103298003030410000d0415041142c1c010b000510780019802d40301b000c01e05034041101c00700e4410399040c003805c04500d032550080000030410303d000c5003042c0c481c00e042a5a90409000c1900c9200446181d404200c82d6542c0000484140c0c0d081e03640b2650354100c09469508140c2c4c04480719550140040c0d40ca0505041103011681c00000400021000e0800200205404941a6050754a8000004008014000450290201d68000e55848116022170040c40541006690640201444256060380e00c547c0b0304424035013000d030050340e80e2a0140c1031002441103d020070f07002400810001030a0701c001c00580704580c094072076003655660382c0201c6402c95040e031101c0b614255400005d08050304004100c1507010502409549035055007907802c0c00d064010040b07440ca90b42d150040a004d000f40206000c1c0c11002c150020302500b428028082c198040c60340b02d40d001c10100f1084104520301800500000d6900710008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 86422186 1250 86420936 86420941
    0x9170a050d0309020102011a06070f06060503060408070614090706140d05090a0c0812030c0d0b090901020301170a0203030301060e0a1a120105010c020901090e030c010510030b0c030103080301050603100e 89
    0xb03000703065100c1003a03003d540b900c19802000f1046016204e03001d54018851440d049440c0c0c0e0706214254010390668529694034004503040d2410821240241d0003019400c2c0c52b0516481c11406079844204050289507107036050115003d0b0000c0c0600035622a82040948002414070104160044404408100e8208414001d20f840d01107551107105014044d8404282c0e280e5000716590300c49800d001d24449270801c0060004203294010349070411a002c004070781400540001400a50155011401d0780d40c000010860b5540c00310001c2002840d440190074000395940000f500c901052103400180f00b4001340d800459500c400c80c5901500c041c81c100c7d041c84130307801c04541e00c94000a06420341c104540300003060070743c040c03442c0400c0180d0003451000e03103030308001ca100042c0840071804041888184182c0001603000c3c021284204420789084c4000c602c0c608014151800117000a0102e2508000600100c2c0460048a05691007603484503641d41310040300007481d0704a6403010489030100d406 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 86423436 1250 86422186 86422213
    0x7061103011502060c0301050402070305070209040b0a0b030705030a0b040c030803071d010c050d030b06042303070e070c0b0405030d020406051309060f060309140d050409050709030309170a05 84
    0xa541640c111200c0c2400a030000c00c0240da642a003a185d0040206042c00104550300d4950010060340f40320385005030501d61198041a899103042d541250308001e0f500402c84421800d1185400140c0201c0080c82c095140102080d02d503800c0200140c0b0440744240080d040c0469071103080002c5a021076811307170341d1400000040003030030b1525809105400503a40b0707080302d43c4a10441402c6d19041000f03400c203c290440190020005861801d40280041c0400078030002c50301c4080321002403106044c0b04200d4808c04250400c0d13015005405400c41400500c040540d0000c1c1d08420305902600d5070700c440d201c0b41081c6203140128440d40700d207140001804120b0b5503110000d03007590901c8641c800c1001d501e40d9186000d848031805184a008000801004264860307005441e0f000d00a002da10480402c141c0428280011401d000f00802c00001e82041050401d1013083ea011203585403082419045a07402070a8401758894015402c66500d00f442c40350005200d4100c816600c84116a4600519807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 86424686 1250 86423436 86423471
    0xa0b090303100609030c090218030303100504061d040f050a0b15010e012309011b0606150311090d03020c03010e011505031606051c020307030f0f020910080c0706 71
    0x140d12150880064500044040c0510b489000380c99111801b900c4003420600400020340101e104550740c29440c12040c869a00d0500c0150f001e6141041c40b0026582440c0c140402e03105070760b0245110b40c0254003520b80381c020f44906503400c6503119983d4103d0001a00303020340b601e00b0800d4043c20f41404c80d002e00c01e0400318401140c2d02d42c40280c85130280315546400542d03862700d01a00c410001101d841812240048140c014100c520f01414a24604505aa4000b110703840b60a4100d600304e83c0e411f002e0007180302e45e0507050880e614600e0180084a1241e5035a0110300418610798003442c1003400050416009004404d124803010780200080703452070205a0203481203810380c0941240800c80407850381408a00e0302c000f0140c44c0310b0340c100281380002c00c07035095100c8100b42a40318160348580da6010241d0004600500507035401240003100102128110b071880301c140d41c0b0386841085080e81075294100300107aa002c50303042c6154280e8404080110b50300c240396008205502d00740c1031861807680c80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 86425936 1250 86424686 86424691
    0x1116020f06120f011802190e0d081902010509071202040209010c150902100e0a05090907080f1c0314040b0402060c2a030105010f0308090409080f07030f020106060c02120a0b090303 79
    0x75000c0c0990444541c04400c0b44034858038038083d140a640171030380c3d01c8e002d05a42001214040c01e0041ca0764008c1c1c0712490300343c01c00c0e4202c15210290304031800e400b5030b0900800f500040c510380070701121450204e00b09100740707485500070b00a680224002c415680104041d600c0030f074011051b120345001d9075507448000c00d11443d080b4800c2c51000c0140c03441d248600009600004050716040b40d0b5802c0c081042040003009140b0100c0d072082c034402113601da1092018801c030162400c01030920500007103426440b02c01c10340d552020107240c08034101c2180a5100e646070416000010403135135413100d002007083c5100d2044503601d00d1040010025400319600070a84d410700c1c20000c40126044030404050036104d0a03c1042d080c11031507801400860745c0e00e001801c600c0002440000c0038001d568402c4020380100040b40701c4118042031442c1815000603c811209603984001c02041d810014090140705104001074010744884602204170340c0b0411004070720607081248039005203011074405580754400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 86427186 1250 86425936 86425949
    0x6031e050117151314010e030708070b060d0b0109020307090801060810180203030f0c0a060c031406010201060e071202070f0602031f0302060a03050606130f0503011116020f06120f01 80
    0xe40283c2d5006541076031680d80529035490800030500c03059100c00f6101c140c401491507065517039485024060404200803c0c90343e10614510b5256446810201655030004045a0080e0408016540011060030700507043d101100001a182c2d03c40000494200c00e5a4000000750b628009012070f078158002060b80c80810340c00d80c203114043c0c616012150071101c5003002500b683c0144690038040b4024406041d9140603107044aa5501e00394485005a03200c14101d03c02096803a0070b040b1220000d2505154410400c1c0000d110301403030407a4503c00040005d18400030007c118002c0124264650101c555164000d20215151642c41c14a42c000354000d942802e941809810400b481c544006c40c070030f003200d070018155800c100c00c4550641c05010020055a4805030820019420b540038000780ca001e4070011041040c1182800113250071100c011920405010301031181003003103c00b0702a030b83c10813581aa40103180d040a1400b1480c00c2c016001544030b83c4105400708510429444c0c7c07620704890382c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 86428436 1250 86427186 86427193
    0x2160b030118021603030b0d060f060501030b04091a06010504030c08010614030d020607180806070206060f0103020903071401020f1903030b0108070c02011d18040b1e0106031e050117 80
    0x800b080d01c5040744501a400c4030b20124100301e20700401d001c0e6010400081003e000c07001e0030b040c0d82c0c0c3e0b91401c90703842200c120705144d80c2d00010300055030f05204451f0715180a850420025103280c40c0e400000c2d01e190b4518105040d62000525182d22500c10b0710002c540c803081c60030309203450394540381c00f81c60203000701d58007140c6044c080500d92800003220050500e10b9009007209441d1010200c403803a8031540d20b20b920a040500c0002c01d094100700c0103128007a1507002d41000e042840030408080403010a040c1090700510241310704ea9030104002049400055141c00b0703c1060000513070800081c081c4802641c05107000510f240e242d40702031600300340e2090341c00300840c10000700155040c02c800d6804800040d8607101d400010350003504140170302c020346c6001d0307084040c0b00340c00504100e9005240d240a030b9100d0b800d00c0100081c0d06105500300010600704403540e01c40040d8224052014880e120800da250281c0d40f0b001c2c20512001c1c058041c141009101d50368503013210041c141d80000c1000340d00d20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 86429686 1250 86428436 86428469
    0x801090c050906030a02030702030708041e0b04080705010e030c1f09060906080a02030601030b040c1d060f090621010609031b0506031501050d0504111503010503030708070302160b0301 81
    0xc1c4960200c5410440c0200303d64210344590414030005d400040091055210800c51040801d41840103003008092142c070041441001d48640d50450a1030ba0103050301c0b00003407105226129000c901841681c03000e19000794114100740000380307055810343c45203400440c0c0700244001160b80000b009920b00315512003800640d0b81d81c40c01c41c1c000c0380038803500300040d101c100070815500140d0000c41e0840c1c5e052601045440c41500014212500e00c83c520012600344202c07140286200d0800e8808031070201c6140e414454640c0c00d0707607881e210301020244101c1c0c0000300c1c1503044403042599058a038100010840b00d6840d60006804030302c7e18007059841400303121030820406020031040d0141c4401a041074116203c625207545048074112200381809000d01c8440742c804514814544030b030b0f000700641d00e0349540c83e83c1840311000c14800b40716404482000184159200041162843c60340000c0300c555070401c505003281000e21040f02c0c82c002c4404c3c4d090000d40240207030061410f0b10100c080365040c48 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 86430936 1250 86429686 86429711
    0x1110c1c0509010c030e0105130816080c090c0a0c0c090f0b040c17090f060f070e12070e040f060e010504030909060807090e011e06080606010c02061207030204050d03080109 76
    0x1070080b0720099000691100629000a01c01c90661140c03c5060400500b0b1900a0124454820301070700060140d40c00170041d082c40d03512007050900101300715406481603002c0d000c04140455401014000c0340b000000b03943c20220320031410000170540090360800c0f066143d4040c1d502a0908508d450b650504211071218185018031500e5803c04103501c6240001c220000700740d0640e40000c0401d0110700507040c503110b07100008e003e000c0c81551048031400c95460302d5240a0407082e83c88c0381550044100001420f162500081c07004140c9614600603074040e5114a007449502ca480c600003406242424641781540d00c054105a01582c42611621411038458200c80220340301032042ca082e0b90b001900c10003491005a01c007050005c0018004942e101034018182d0b60308000d202c14280555940b602048507101c240942d5400c11024a400c24000c040703600041c3d071900036440c25403a811809000f080e40b20b8001d60484000b0000501101c4550040e4107003d850108248501c13003002e802e004e0b020403030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 86432186 1250 86430936 86430947
    0x708010503060402120c040e0609120301030b1503030d090302030306040b0f2803060504050f0d080c190309020a0f0e06032e0605090c030108100509071701110c1c 71
    0x140e40c0080d00400b030030f80c0c0c0c0307400300800c122039a0040c076094046d0105040482d1200d014114102d6101c0005008078285408818a00300c4442502d0310551428001400040c40c025007558002c40d040c41c2100c0000d501c04000b034118450300004c00060ba1030080040c3c20160080051071045108035002c120002c0841d0501c13a081d020342c25559408001003980b854190408071261003a240400c03252404aa1a1390f620012164260390503540c1e40e000031806042a00104481e01210940e413400e8807407420100070350401c80c0205c5090107550b190101c1c601003414801d034400d82c81e094009020f584019640c1143e141c8142c0305000b82040744000c10005140c0d8140040c0b5008980b0180b60301d03250100000e1420052800c1c909000c50119031140d10019555503050811f030b0080e41003185c0c5c941d5030b501d00341d0414034041e0641c920141050626042009000010511200711100240380f446a6102005101c0c0104030000300600100c0000c5010b942c0300500103002c041c031704120311070b035900103030b04c0101503a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 86433436 1250 86432186 86432189
    0x2a0f080f0f0c1e030a031e03090209040b070c06050703020319090203030304020108060d0b07020318010201090f0b0c09030102071b1e2912060306060d150c051e090108070801 76
    0x800b82d1101c818004541044400600f9128243c3c2460a4481008000030b050880c4400180c00140c4042c1201c4541e030702c2d100402c9422666810304001000e100e03030104420380b800030405800380106070300060100b0702900540c82090380c011010405480c002c00d01400030341040c0c0c0c1818060a070001c00016202241c0b2920003206c0e0001d0045045560300e90044480d20001020380b500100318074121400903a0f8640981d02581c3e040d0040c60300c40b111650f81032600c07069805a50704680c1003200780380200e41d010703441c5032940c0c2c2c0141102d4500d40d50306518102c14030480b0009609980f00188010a1103105440ba03580fa00010783c2d82c1842d00d0740c43e940807002c00e00000c00c0c40305602c0590000c010044003040c0100601040703c00e200101001c019040145800c0540d05004503035480d01004814607040c030000d50300450454041d2031030322054964866444c00e8036103186409940b201108090ba019809945a40507000c00368900100b17286072015568000840b01c6021510030001320f013556000e60403460 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 86434686 1250 86433436 86433463
    0x1a040f230c090402040b0d06140c180405090c0d03200106061407030905060703030203060f0307060f032c211e030a09021c020102060c07030801032a0f080f 68
    0xa21070a1a008201050202901c01c03a4005c1d44d41512686da501c0e60300c841c540040c0104400510030301b1880384035059803001403810b14142410000740311200c149080f0142c041d0020f0794001419501c051302c1c2407401c89110030842d448011507069400301075102d80c03002c810410000b080b0030704200030080c060a961650040c0004100c020003c82035407104003016015a0b0700030b14202d60030305d07520f2001c95425405080d083d000681c0010800020b405c3c0100d0049a480b010390042405600d4004003c0807200c114140904141d1584003540c4410701022515152400000c95014250040c580180d9240500803c61a000c3d41100400468000c1348040d54251200312088058400e030001200700e0740e61004210711a0150b40d61451409a02d42c90352f501e80c9a05c1c59411070f41d0f1001c8a00000e844c000000381414001c403070410810300003d0b48885c1d21030450385e010044041400e40340800c80d6085042710301c0c18020801c4a800000c00070b00d200c042400325500754090f9560b501c6001700c1c15480700151010381 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 86435936 1250 86434686 86434693
    0x10606020d210513020f09010305120c010204050303030106080906070806090103020d0819050a02190c0e040311060703061703031b13031a090c19030605041a040f23 72
    0x105507401440b441000b950003614011a4032614041641114410b4520152024415000f0300841c1051000000c04000465001402c0e40c03450350ba0641e280c4d02c3c500800d51960b800315105a0b100740940644003e054001c1c141c0c2d86943c0c40c2e80380186136100c06c60301e00c659442520f0100e0062030103144a01d018000c0503005404d035038251f40a00008408107501100c1c40041049203024801110000e00c4110103180e403182d9070f6950b445070081c81c18143c40d500349d5030600d10280e240300003400b10030107108540b0a98030401d0301da0b5407030a082d1514010003e0454031401403a00b004900c9525a0004040d911030401c02100e1441e0a50800d581c0c2c0400c848034030302442651000302c07412204002500440007881c40c0100c80a4407542c80c403103404002d1860340b0b00500d10200340075801c9010310402000d03160030384850514040c1c031034100c185c0204a00c0003605150741d034400700b800c0c03119140355090031814000ea40e03034680c00c4c03900d0080143c1a200400707480e914000400242d007880b211000d04002e0f0a1035004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 86437186 1250 86435936 86435953
    0xb1905010509010c050a0c08100e0a06090503040503070603020403061503110f1203040303030f050109050c0f0a03150b0c12030903040306180b07020d020d091505130302120f0c0301060602 82
    0x10740321a4090955941070080710301c2c1060000345d040022141942c0706d9014021501c0c40c2c189a9898186060030f813401a40c20500c06a000310b01c00900c401c84030741c109101180c0c0c40c078030342001421407049802c89074040c0070f1000b02251042e0550000c100b100d1203560104480036107031a00c11281c144034000103182c85402102035a80345801105100c1c002c2c0020b000d8240404400d4100c1d00e164460780c8110080b03030302c507407001041c0401c901c41d0034010055080d0038003003403a004a5901ea58412519002d00326100401d4100d000c82c440d0303200c0c81143c03001c040004120354941000e0a26a004a9001c040c10f21070701446858a0300900b0589000d100010000c604090440d9503983c0504008044441c0d540301c03062100c8042081024460f0050001d074010b03040b141001c0e0b0b4024180382054903010107010a080d001c00107023001c2d6031040101d81042c9440d40e02c0c0d90303014a100090a0403640003a5006024070301080c0e6400c000314100204d001460301315400940e0050a01d030980780d2a00c02c2da40940c101824 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 86438436 1250 86437186 86437189
    0x801050607020a090203270703020a0b03090708030307110f070315021810030204210803010902030703180501050901061211010804031106010f170102120601050f0405090112060b1905 80
    0x5007203524402445511078549078280f403822600304480c02c2c4442282c6072807858505d0000000105c000b15030001405417181582c000c240c00201510450440280c000002126841c007030040001030318500082d40d607207044c013180060130450000002013282c0200040079503000c50002d820b0084a034003584c0344a8000d0b001c01444003e41004040b00070010b441406a400307562141c1030121034059030b4900607212424003004052111503112031000103462840740101048844041d0780c1114510000543d80381d403a4071049015081805030b01d1000d41e040d0350002c1c1044010b4108506c120590300007044404d55900702400180100078001d0305162501021b8109948200c0c0000d42c01406030808101081c1800451450000c3c245d00600000349115000d100c41c018081c0c44c2c47c4602407002c029070410b54038100391a004880607200506104000940c8299070b01600e0513038000f0040180715151035a500c0d0a80c44c460000c0354011502c2c207203043c100c607101e40f5150100d0320300c140c3d210f000d50071075604140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 86439686 1250 86438436 86438449
    0x602071a1305060a020c03011409060906090c0904030c0807050a060c050403030c110604030b010e0403030c0e0105120603120c0105060922060504030302120c070213180b1b04061107080a0201080105 86
    0x100c04c0003140a050061134041c0c900740101400b01074192480c2400b8580f4041c200d04111020b00b02003da03811003001c0c0300106100150b048003416048030303880c24031744a51506460085503c00d00400f40341001c1400002c0c0100881c8041e006030140c40107010500d0f101307a00301c0d00e034461800010041541c241100021500303900006100c0c01e0301070000d5140c1510ba88030009028426440020b44c801001c040008040d410700030300403403e1450500b2418a5403460002c4d09038052a05030117040030052001400035a03003081604024500c0007006075558070b002600078003800c0c040b02d14a0061404a022640c40307040f41100307070803010a0700c44c10040f50200e90307518805808054401d808160b02805000ea21040c1c84020901640c5110344503a9035140074418010741854140038407007001d00e01a1502001144881610b00785940070205240a0340e83c0e240349005d409084200040105020501191854008440e4002c103801c5400f150182d59440b10b046c0e42d038040200009001075a0007004010f03604202 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 86440936 1250 86439686 86439697
    0x204050109050423030d230112030906090506030622050c040302010e03060702070b03070504050a090209090714040504022802010c08010e09030a1b0b0405010b0111030708090f010c0501060602071a130506 89
    0xc7c80e080701038450300c0c414210074081c1c001a0048a00c500c0500825400418000c020410350820740720603854140003441c00c0c04000c152900803009402e0346144500024840c481078a08407804018500300a80365582c982c0007404100d0109103860015031240c81c0000b5018440c160355401001d1860400415500c16000075150505002d41800042040e079102c2c1254000340180310b0006885444801c1000b4845d8005044941408260340c07251980c612407100b11010b54400341c0700503a4800070042158403250011040715042d8448290b44900d0aa0640100c0d0f501000e65a4511550340c8a0102e08002c01302075801e841d6960041103840c070114020001c82d40505a0b50040030044e86c45502c401c0090b60f412201100d069544114501056800c8039041e650400d080000390304011282e550005544640800e0622600883da04107050760310400540d11034580c440003c3c800507540c1c2601030740d1011240508a81040721140c101010441c010940c1c10035070340c0081c103161240c5441c007071240b03d5125 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 86442186 1250 86440936 86440961
    0x30318070b03130c0e070f0f0e0a090204060201050609090a0201030924270f021309020a08060402010206060414060f041b0e0a0504050106050d0b0307030204050109050423030d 77
    0x61250020720005510080c40c8902844030428002da00e161410030310640c06034001410f101104020f000425500800a030108045820200c5412201d00d030b041d1641000c403500c0703540c070072501080855040390300d03000f44c8111441d039002400076071165420001c80c841c0841d900c0340d2a60100b40f12502661184d0811054540502c10340e580034600c1c1d0103110501d400301289811101e403640566000300c1c8000700700c501e0440410410002c0c0d00d005540712058400c46000180c030443c0d031860580c0c1481c0403070340152500740d030080c000440079999003103860b01d4040c111416800760290000180550805000b200045200110381d41038580d218010411001810203026400c01d50b1090448070040010300f450343c86500588501e04d60040c2030080140c00d95541d00020f004038100001001015080b00555100306010035011420b400147c012a1601c003d907400070358000d003810b000103071900c01d035032141c1c1c000c5000c3c1503c0c8144c03040600a50300800180b51003851140c2c81003001d001d2202407a80300700c206000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 86443436 1250 86442186 86442193
    0x4030b19023c03100603050c09120d0201140606030402040c2703020f0a0f1a0d06121103010b1309052b0906030b0307030326070e030717030318 63
    0xc4a2041e0101010100c07011a64858039002c1d0500d9001c24481c80d840201c035801c52035185207458030140d049560307184104c1050503205c1000c580b2401c11107058400554014140361381d8000b19080465840c0e41c44078103080076502e401c241c59202000700940a02c120005000c4620b151075076400d000060242506240c2006841d6100000d100d000c0003880002100354080c4500543c114010030442c010246401c911552030004c00700a6a20b01191a60854541d0b400185894890321007401aa1090340d96804295290150215510303501c2040b046802d40901d01d12601e1280c002c2c01c3c10f080b10340742000140e0068200c5500c8a0101c1c0c250492882c15104409541d00d8800400a00c1c0c04070b000c5007114015416099818041c6c04d901001d010010b2040c0d140500c5007803500d101090f12841c131400064100520300301c040304109004030b83c01600742991a8210503600e80708100814900a02407003d210b405240d00014403140001c4200100c0412940554950740700c84000395440ca40c02e644d070040900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 86444686 1250 86443436 86443447
    0xe090a1a0601020a2f01020105040c2d030503040e18070b09012102180108040b0c07030309080d0e240f0a06030503070b09070e010303021e010b0a03050c03010b0604030b1902 76
    0xd0b0701500c5102e50700c540c441d01c2e000c019400c000e1080c0d00381e520014035046a02d4001002b001c5a61400402e0468000511910a0030b144c101c0903a40440c04905030240480000400401c00000000500071250320b8414081c10303407102c1c54a0b5541c02e000c5000300d00703554840b20341071001040040090481c10814140150b010b060030000070300036035081c440c07600e1141e400300d820f86d0b0540340c04041000c4c0700d50074a00802e080c60107950b108486000544404079540c07012404604140c0a80d10801c2025000a000da44402c16003003c5006002c41c41050011801200322003404101c0710410000f002d80c0c2c44a4205041d586c8040c005218840100b01a00d0907454050000208400b8402042c0c114098004050300303192441510b4038100082d8014043c4002d00001000804e50100704000c0c0180b012101035400200d83d10480e003d84112200341390321196116000040000014400013048000e400901c800d013840000c01c00e10380107074800642400c40080015400c1000d00340c24401009030304a0060512 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 86445936 1250 86444686 86444693
    0x6071212150f030c0501110a08070206071e050d031506031104050603040803040303060b09100c02010e030d050c01050f061f0201140406090209100308090402161401060e090a1a0601020a 81
    0x450720b5800402e04a268040500601c440d07640300c00c01600085c2031084042c41d21207007507582c5d070305170200c007500180c80070840c4021580c40200b242c6180c0c1c0c101c2c90b207801000103051121103a41300d20400f11294440d0407480d4296074060f00500780c4050021030540507641ca4400b050b8058815031071107441e480700410020036a0360310800510f0280303000b80e0b110764580c03a00e0720700034040380e001d07401030b41e10804140100c00507603946c0c54106444500030728000c1038220207131005952502c1c40711100d07a81070003000f1103123548550100c0540694007c0000030300054992100341012403030162151500400d0113080307960032903840450280b0703914a0b0f2000041c40c40c03003030f100410644800d83d000c0740c442d51224008002d40c83c10354100c80e0442829049070416500d15030b80c0200510032000d401d80926004540a560109603100503103159030400703003991443c1585000b01d030081c445402400c00755084100403d5000c207000510413a00f42d80900380004150035240b1603166107400400e114110310a040010000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 86447186 1250 86445936 86445971
    0xf010203070302091002030c1b0103141614310801110405040c050307020a020f0609040908090103060e090c04020706060b0a1701050f0d0b09070503120705010b06071212 74
    0x58001982d00503101d07820030f0100110f80c021099003004541c010301414400403004101050107841c805801e03903140d0100801600a01031600d8803000a501c000200810901c260000d080902c0d03040d03039507440840762038030042040d002d40b512641e035070348600744401a0850f0f81c04051090800c07880b07800b020a550b0341c1c07116007510204942c02032201c00104080080303040c070b4000c8000211003400d00c5401c510346001c0081d40c032072412501078440c010035070440c1002d490701c0003180d91440b80600b040c01014a1800c04006d43c0e402041d40d140000d03c0c003400041d1012443e41c1c0e580c01006000701030050035040701c0801002e908480e400782c42040c3d40320400101d400c00c00c0000d00441c201c98459000419400744480d8810030140e1105010740b0548040d8400c50755404400b07030032540d0100c07070b1001e90740ba00d490725481c08686811440c2c042c070624044038088401d9030090050503104e040240640742c0c944007030245034040c2c07800090100300050302d0100c84a0240b02d200004a55041001820140c1407804912 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 86448436 1250 86447186 86447191
    0x4030819020a0213090c090e0312060f13051e0103020d0305070503040e010e0609100f0605130305010207140f011806020a020c1021060501090e0403020c090c04090c0c02060405120f010203 82
    0x84ca40c1e80781010300030084c04d100480010119480b08011681c20455400c0e104e2003041c424010485d82c560000700c40386e40b10034244107041006006003082c0c0c2d100c1c032298001014140d401342c644c0000b031034184502c030462045460503603a000c1c1c405443d21242e583c0696031030f0480c50302110325000522000c40d4001c100c22105000b0001044e0594103401c02c08280801440d0107062120b00e0040c020b002c2c0441c0c1a07918406045981510701242ea03201002e1200d006145a500010629400094042c0030300c02c0c03541002d4081c16145081d901110714052004e8200d03400300380c0c01841c04006107a2400030902d5135020b00318000d264016140c42c1d100b5080010003c08200d003404020400310303900442c0011011000d55414080c09400b00107440c00d044c00600a403645100d0807084880f014000380415109001e48004a480542a4503090030801424195a08507000d031030b0205d8602890b03100c09601c00e22800c003801c1e401800311840c01e41400c0a20032008840226802e50348940e162410000009100451 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 86449686 1250 86448436 86448469
    0x30c012a0b040309031b14060c01020c01020d0606020714100c0203010216030f030c030b06070212070806040609030f02032b02120c0c06100e010e06010e101205060604030819020a02 79
    0x1c03442c0e0075031825174100780c0343d0500340001001d42d207018801034400f8803201f00403c2d0101e641c01d071200300700d020300c50282c03159801c00ca04650010901c11041101340e0007000554289400344c800b0262030b02c59510460103002c24080d408641d41811003240c500a030580d0582c1400034002502e0702c900c1ca0807003040c00840c44011000249200c1881501eaa810300c1444007050040c5020301c289507005002409034051548040d11800b00b41c50945190716003002503400a100030303020385419181c01e080440080c0b00e803602c03c0c1c0c003080c2ca8800d81c001e900d1002c01201c4800c40c82c0c0441c9070a21002403810014003900e45d02008803030303a0800420740401c4c40c1440e03d9208460741d0040315a2240e0040d6001d087c820090401780c08224120000d01c5004000d80540741900c0c8209030080f042e68403900102d843e03c181601d015000300543c03003621901648002980c1d0004030b1103000f84110f8031100d041c13090a01c00da00c8041d04e00342040c00f0781c141070004600c42c00c1e8400090300c1180d5980030580c0000b00c2e007111426004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 86450936 1250 86449686 86449697
    0x6120309050103201213120f020607050406080a110d11030108010f0b0330030403050705010c081e1b0408150c0a0f0e120706051206030c012a0b0403 65
    0x400c4250ba06016921103500141c2501c1040358803895144c10900403905804c42c58005080042c0c9030440b58a462101183c000008083c003603440340000e088106c071358903158010f0058000181d0024021002c81f4212080e0b580da200650303486064ad04010016544944040c00c403c0003c0007248520b030041103018540210300d0707a41d0394900308003242199880d0806200e42828950000817542e00031541f01d4031803024410405600d507564107120b0315074110f0320000f0140c510200500040c03580c4400038080b014400d030001c100e10110404150b40011040301d03521000462140d45030341c0340d0b8012500e01e070000d00c0b4411920410b20300240c4000f4a400a40000844c0d6100601a0040c0c07110b040125410070b820f580c1451910754414801030080f65110b84002c00d22075035014071425a01c40d110710316420f01143d8141c0746400e03180d520040103603110010000160f079040c2e011440c00d00d002300305034500e000c1c141c6803012480e510050701031718640f00700003c1120310081d4440c48041484051502c2c4150302c240d498 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 86452186 1250 86450936 86450939
    0x6020406021b0d080a1409130207021011030906070302210c060a0204030f0b090c090403080105040c140403120207080a1a07080f0403080604110409150b0a020309010e010306120309 79
    0x61070a100700e0b00714640b160b90150b0481c008a12988215040741d0301501e00941200841080c1e0f2200e48107404200d43c110305011203072a910141a4044c0000d6403080340d0003003044100310390842342040e10f00d000c0091074000300460040e078a0b100004110b0b00d4800d00540751003c42406462411800f18481e017041c0c40c0d80020b403416450024050158492079140701142814150707260980100c8020354001d000800303ca01054140904100080034400000d0800d4a9490180fa009220440a00c5801d004506005046005501445900780d2800b211440300b4101480d40d1102a143c03e50341c000700040d4001c1a1000c5028007045c42141552406030304813a240e0080550a9031144000401c004c2c00c000917001404042e21520074011340041d0189040e14554841d10009401000b10005015107040c2c00580080e800c1c0342d5410608146545544003100c40740c3e540e016a406215401e28603006820400c4494002d600804142c100040180b40c006440d0340c480903007000c46400203200394081000d1320700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 86453436 1250 86452186 86452213
    0xc04180b010f0b0301060e0609030607031505060f030c13120c0303080109020a0c06090606050d05010905010b0303130306050403050702090103080d0e1c05030a0e030406091e051e0d0602040602 84
    0x911801800040207400490340f82414264040c00107000d0001000200c00326060305035501c00503500b00c2c10004013078404506000c40042c0007019000451281c12a881800103214a0840701341c03014585400e03d0b140c5156144041403c5a030f000b8448006400c1c074821011079070041500010350074034404c0701240e1800c1d0035810081c10891059009088043c01048010f0706a036000d00d04080803a802a400b180d040c00510303190001d050140c00a0382c2100d074090448040c041c05401c2510f16070b0181000b0400001124181601c81c400d484140490540715002040099a6540002d50050092402d1820074a4990001f18914001e0340140e500d04008280108072040c584110f0307002d60410801081910f11001d61007000450828019090000210004000c035545411034000c0f00c40d040140c1c0da03165154600a80980028020b0f0300313040d03000c0300c0405000711603010b0150580f00010a0b00460703001403a04150450920344110303810414000035900000c4880c00a0b00240a40f500a001038409410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 86454686 1250 86453436 86453453
    0x304080304180b0a0b07020409060605060c0102040612020405010804020904050703020301140717010501021b0d021302210c030105220504210201090b0c0a0c1a060114130504020a020c0418 82
    0x10300c5038400c604d40301c020401d2801e20307411910f006505690104030782e031403420320720002d144540c0230b181c0000001400350702c04070f810b40c0180240c62140d204c51403144600c0c0c1c14102240500d001c0c645c0491036910201740545407203804079510500c1a021100390644a5011038250340c007036140d0341001c2c20484140003900b5080120541446212403007107141c0c1d8034002c0001d5507134001c41820b00c04107040d90310101c15900c03079103800340a07560043c1c07601c0202a4003500c064001e602c88101418010280640401c011080c1485503019040c0d9289241c25642018200401308031420744856440201c1c185a200122050240912540c00b840c9903101a07441c00083e00010b0080c5210031045915021413200061811140c0035000340e0701d803620350749031840700d00d041d40c641c0c01400c00507158049000003005078458a030651072013120207a8071440c11000451203141d15000348141c0ba2891038003081e05008506283d809408145000c0c81195903031005203000c01e0031580340107110b4042407200f2822105020412 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 86455936 1250 86454686 86454701
    0x302041a0703020a08030a0b03071205010506030a0809060f0403140a020102060619030605070203121602011505010f120f0903050403020f01091a0306150309010903021b0d080c030408030418 83
    0xc0a90324640319903560700035201c0c2800c2c80028440704010010038000344280e88800c0a5a601a0845a05a0322011800218485003204450560804c000544075060101315210b03c10713070242080d420000c00030100113146c3c212100303920611a00344000008100c8460f502c015080c44540501183d1445000081c1402300007400c0f02d004103014100e028481c0d60b081a0f0200701ca810040009081e1076041c1c0803401c501c1802400c0da0056502c000f41704030790005041e001d1105110381c0082181c400d8031038014228104074821180400c03000c0c01c40b4801c150094200c0f800500b070750100090068100b0300340d1400c40e0324800c6c0540001c2c20205040c0114148105820300c100000d003820b0b1082450014000126016a00d104c0c00e103007004804110140c4441503d00c0d901d50200017559140c0c81d00300f0703d103402070909003000d5005206211040107000584400c42200000c05400302107510060b844003805a030002c404202c075403204210005280c07800740050005882d40021900045043d4407078201913f444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 86457186 1250 86455936 86455979
    0xd0f0f020a03110906070206130302030114100f05010804060506040905030a09031703160c03030f1b18080601060c080c0a0614090102091e030123091501051e0a0f06030204 75
    0x4c002c411450b40e41d1a00740c035252541140c10b20303a50081030b5000c12003410240d00081d00756092030300c0c040d10808403440c8607114407150800d00440540d2417454042d811200e20646000c143c8010104000c20a00c0e0040340e8061406003000c90b206510ba0380e0b0310b1540c0c1c0952451000648584018010401040c101c43c51507203003c044c043c11410070501190741c16800c071365000d00b40104401c0540815000b904030400407201820100011020003080c24203401d060440880061b18454006c2811a5008003140c2501c044134000c000303683c01c003001030702d01c03c1ca9440c1c00d484052003480b01802d031640c104603c80100d48182400301740300701c001800d04401c0201400e0100e07582d006125041d201d03282c21424005110100414000412180e07000c00d004000c8241d04051802c5010542d020309140c09020b2030054030a0000c48008a40c00d06010080f02400e0003055403120030104003174901c1c00c40c1c100480d007440000b481c0048140d680c59480d040d401056100c0000300b500414200a66460510340c07040c131106 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 86458436 1250 86457186 86457221
    0x2061609030210030902030a08030406090213090b011511070306022d0304020d03030e010f0507080c0a140721022109060904050907050d08030901150b0f0d0f0f020a03 73
    0x107550014030418128070b401020980e0398122070f801e568040010034101a00300025660b07a007460704110010717006120042c2d00550340c610000e000030340c0c07174480e8a108036041604500c569080c030500800c1a0382d100030900800c541807609928a0005000b048000c520070000169248000180c460000c03850b0420746410051106039102d5402000045a51055049580780c01e514000d00d01503009049600d03d465666180c001c03c2f84904581d640b003503020310441d4036032504603039849409544034410519004000342800381c4e103440111408000d03121302c44c46422105a00000c0031550002c142182c8030120050340528107022480491a82d1203c60360340d04c0c40e040d85070024440100b217881c450904580e00641d0b40e1800150f0109050010380c0c0a080d0080025a02c42c51506054803283c0054034411555481e0000200e422080c19103c0421502d5504516041a00c0458800810f0304450510892551180500c0680103442e00c10090718544d20305005841e5a088940102219481420070b00e0008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 86459686 1250 86458436 86458439
    0x3060f060a09030305030903040b0703081b090a0e04020f0306100e01080303070e0904050708010c03020403030e1206060d14241506090d06091e12020d0c12020f0d02061609 75
    0x1503020781002d0640741c040c1842607403600d890350807a1a51041d54812148800041130120030035500047c03190051005201402d00d100c01504170000c2071140c4040d481e40003580c8141000182060f808095002d40014001400f0020506c0801c0c10500708560b00d2200360350500c0144002c205014026014100c004010341c294035005c140641382440075080d8a1041d044000000c04002e401c003e1000501240e00007804418a40780780030b8040d4215010440128180c440010000d0500015104007000300c000240203580303501040c0003404080c1c0d0001d44144201c800786075000c480c1045650321810850110b108200c40b414980740c01c1040142c890407980c0d2000100d503070f60782c0d24403003602d1b54240c0c21251514001d549182210003080503034001840d90340c03441414405640309880d0350b1096400ba51140c0c0001e548014200d0b16252240402000b0500601c03125011402c0002c040006030094012150660f04500350750b460038030049100c1c001a84000108400070f1182c2c1800c1c403009034103041801030503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 86460936 1250 86459686 86459707
    0xa0e07022107020d0c140301020c0a02040b061207020703030e0f0901061b050f060108070b04030506040f0c09050a1506170c03040611030a090515040803040f05010b060a030203060f06 80
    0x1c03001c00641d09011001c00d8030140320120440c0840d4071190b4000c040f2219140e4524124102286900c201c6070484141654440b403401d06000b11007240c0c05171009440420740359420480145544281980c002406000c03100a444004440070700a07080d5400030840349245140042c19840300c81c040324001e8207000e6200c8000d454126000e4150303019420200c1451100584040c80d1a00381c6401410500c85c8040c804045107004c900a41a10126010f41d00c07850703103c161410292045200080c01e5902c00700c0000c000c00d4008000e1000b140c030662400840958441400c400c1d10380544019103c00c0d42c60000311042440d07450084e00400301790500000d036490b5008400c200050041c400400100d0000c0081c081200c180d0211407415000b004a507280e0400c0c2c1c04500041251041c100c901c2c1c402c804007035440c4440015454480c9501400c0c441c03540d500c03030703070760036009142c45008588540d2144060384e80f0707039954400b51058901998005840789000d2040141580307803141c016003e0782c803c01c11040c06 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 86462186 1250 86460936 86460943
    0x10207120c0b071103070303200a0e030c120d050703030b04050a1a09190b040e0d05130603050c0301030305070323131401080c1602150705010b041e0f0609050112020a0e0702 76
    0x2547c0c040c10000b6000580c0c0f251034102130b18414901210f00400501c083c2c48c250400c2c41c1c000c44490950480c1c983c0d04880d001c3c4000c0d01d0b0501d00c21200f5505c40c0c494502d9142c4900000c01c0c907540f1a140100341d101a1101280c141c50051381c0050101d0303240c2c040100c4882240300354140042017101c101201d030910104800340030b001c03649461038464035403640041580340c0e50080452040e0f20421070761080d070b40e0740004015811840031301003402012100040c5652085c081c2a0007080c40031000c07859a4a90390741500d60b42c0c0309681c11000e21440525000e0907290049155440054030b18034299601200c2e204243d00c040c03903070008200100c070100225101d036070004042da03010800c2801c0c0780e42c9100e001042c02c00c00340968000bd602405214520340f00a00c51030141200c0d80c80303071f4003d01c5101c101e0020841519164104007800c003900300c048007205030f1160400300300381c50031010005190391180c01d01c0042d54000d070484040741034031100080c118146503801400500100c58512075904001c84002d44 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 86463436 1250 86462186 86462197
    0x61b0803061003060e04032a11091807090609060807120303050402030a05010c02030909060906130f060f080a0302071d01032409060e01050709180e010207120c0b071103 74
    0x788011820010b1124081d51140020f0000380d0300025841c070341450000d1030b00c0603e41450421075558002026802c07070384003c0c1c5000aa01c224045100c2010030103001c101030703004001080d0078402d42440040c90205000b5030700504000540450f400e81072400300800e803811640440d14036401040100000d055818011510540c5440c02180030f032618000646011109000501254030b0507002d16641c9030000018000ca09064500d807409a0301e440030810010001c4800d01e801c0300d451100140d260740c140d8881441038a100100058961701d1300c0002c65030148030742101801c2e81c0450780704014075404018000040088400d506020355040081610485062200a0101500e460300c1c000c400b178a46000300c0080030345c1c50100003000c541c1c10b1a1001e00b413140444202c0d9443d000124120030300c0390215400795194031126600151090200500800d07245074045500e560a001c4140017980715110401112540da1701c80705042054204049130b030001904c54024858000d01607a04c2e5940882a03c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 86464686 1250 86463436 86463439
    0xa0e01090e01090803010e0f160507060f180f0204050a020408071401030902040c0c1101111905010b151803010204030c050d050a171201142103120f01061b080306 71
    0x441c14141c0501c180500100d00c0300800104c0c002c000412450291140c1a00c5070001600c1020152100c0010b82224400400e442c0c0004000704000c40116445400010580e4242d003000540c0c40300780302038140e0960405800b20383c5400d0b000544d80075490320740100768200d03034194811850301e4a41101d0a41d15144c034441e42125954420042030f59a010354808061650050000d01848690700d600810581c00805c04880c1f0221841c03003015654850500d17029034146003802000c60420500f0043e00c500c0120703408840320b648070f0802c03140b0f5860b1020714100d508404021142c51303650308564042e0140740c120150740a40c0c030500c001c0010030341d10500ea034101c4000b40c520341d103032100c5410620304168400e034002d0080424100380501034440f0701d00400304007030054040b881a9880341485002041e580e086554003035410090045d41e01c10324040ba614080c60b8a0490b0b207016101d42803008020001c8079001000b2011400420203e608082402e5035000a107150145842c0030303a0702e51805000103840356 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 86465936 1250 86464686 86464691
    0x3010b0d031202040b0316020f010902030d20030406030507110f03040302060f0c01060b041503020702060301091e051510081006110c0303040312020c06040305070504050c0d18110a0e0109 82
    0x720526550b9040b2005044400c1c032080d920b250011158074580d042047c000010310842d000a200c0c2441071081e861074913401001351001c0101c0a00c02c13030b03420124110fa243c480c1107415450340054410801000240095100814286040c90019010805800341514150001107200d15602c0d4044210740540343d0488a00c0c6c0c0f55003e000360001c007406440359a4006602e4050301050b15500d10021713000310307031000c8940c4100048104d0f0031426405030b140000e40180b403d000600c0f9050080e00030326a01031100102501303001000801c1010b03100c080c2c501f20400c2911845500d494200807601e50390754549410700d284141800d001001050300984144400c003c0701e40185c5641c02802c1c03041042851000f41100d40300d039200e08020b43c085550082074805441081758160003410702d1800e40b0120b0742c100d0041c1416615001c1840301501d030040103092401010405802d800072540701e030140005c1c40e03115001c00c1ca041c0b07103045007441c0d002d540f01e981700d08552a01002424210642d45041d20b002c100c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 86467186 1250 86465936 86465957
    0xa020a03080a1404031808030c03070f03020a020d080306030105060d050a140f03220608010305070e0703020f0d050601030b0415060c020f040207080a0305100e0106180504150e0603010b0d03 83
    0x400142503c0c4020040f116501c3c2c20b0105240d8442505006003141a40380f000d0682d946031803598910030f5071044482c607001880a40d0100c0c9100302d010720f45500a00607038283c0744041e40050300074040c5c0c0404a454208c04801c3c00010705092081e40d078090300c180d5101c03121a03080d0f10b07078654445a1a0004092902c0c940341810081828041c0d40314a5410100b22526407040150074030703080e0700180445042403101d0b44c0c00034005104000e664104ca030040041c1807010b040080c12121030100824660905800b00710300510300340303210700400310b205c103c11000a035401e03c07800040950300c0c0c2c1d4980070711039410811400d00307111035801c1c003104544003410040f20030b03810762012601c0082d210140c2c6900500c08201d901c14040b13141d00400400030950380800041e80e0b80085d905190155004102c440121140144000742c0140c5400d81030440d201301d030140c00f95450300024180c900c038500c6000d8031100d042c070070424103100c0e40714250041e0b8120020322103030032104081110165102805420001c11026 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 86468436 1250 86467186 86467201
    0x6181b050909101a0901020c0a0b0a080702070b0412050d081506070203120708071412041a0d0e070f090506100f050f07030306050112021207050901050405090103060f110a020a0308 79
    0x140c80f8020052510fa501182500500d541000e411002040d405805583c0c40440d0a103010200c2c0c10541d104c03014401d003001c0400100300c802070b100400d14025445103240205030200c4480203440100040c00c50000001c40c21701d406800e00a013842c015051240301d0082c003910308071403c0540103c45040d10320035100da0040c00060f02d4104804510148903100043c642c0c1403000900003000024001d071035218a0758100c8946a036584651207054030203400510090250100400101080750b801c81c01d00c609010416900d0703821580361608012180d481420200440c1101b0b03e803250081c142a0710801223441c00f5400700c0c40340e0038441700250400086603000b074a403d000308196924055003800250715282c20745006001001140120342c0810400d541c4403415041d5402203441d5014030170070000183e15002c00070348194200c01c0115042c01000e200100d4661100100980218083c48001c2a201c2d445030848085602c0a0750604e0540c8013000b0320b010158000904003103440e45450540c40c540d94119 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 86469686 1250 86468436 86468461
    0x30615180126340518040605061303060c0908030f090d0b0115020601050f060909040201021c0504050a1d010b030408121503120a0c0f060f06181b050909 67
    0x210300800b4106a182806108514884a40122805040b0703042960340f40c1d01c51038880300c80180c28040050000c00c003442056a1542e0303562a5a2000741c03003c55100d1300c40740082d94940001207203000710079600004100b440031034000c10001c0e0a450402c032141c1424418941e440348140b019012014000145150760b54a540d000d03408080d4214400007182e5031550140b0006244000f82000148144800851180741c44896100e0a03040201800e280c0900c000502c003083c000148143d0641c043c41442136050081c15540d22154140d603a42c003980c8505040070010022551340000019180342a03c21403911410408c01d4103648140712081c0d125074543c03500d08402c1c403846030481c8003000d000044c85003e083e180e4111000110803002e84e0342485140b00c2d040d51074017446a02070002445030800c1000300b000c0300c0da2406581d00441000c00c0c4109407500312000c1d076006900000c02400046034042030f03440b01c0d101c1c4040780025902003d500c0742120a000300341c2d001d01c00a09100d16501808607180f8070840c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 86470936 1250 86469686 86469737
    0xb060708070515070512010504050f0a0c021216060e0303060d08031302130f050f060a0b0a02011503030e03070e16140706060801020409060509100b07020109080f030306151801 77
    0x2543d10140ba803801410062490b00090888032448080c1800802c41c0d107028000c5500c1002c0603196004c069803007050010242012191040030350113206441c3c0c2502ca0b0b8000104160781c403071100207800060501e4140203e0ba860108002c982d001130050000359a5000c082d00c498a030403001c89510f03519603c004010764064600e000358842054007240c402002e054001c1c040000d0f60040820180e540e003000488180300840d002640001d0000080c4524422100504910103182c03000080005140c00d854103007800a820917004140c01031450120b41c5810400034020b40b14a0341c803581c0741d040035007492500340c65103a00e08040c8026000c40030046805903095600c4e07203801601c18404996180b40c024001e40c0180142c3c8162401d140001c141c9080515240b80100031407030103104500e25008450b200f0740c000c00c000301e041102c00000000c0030041000048001c14181000d19a6404d00da410030101c5e505844800d2002c803410300462426400c9200340d040d4180003820030071254900419164284d1890 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 86472186 1250 86470936 86470963
    0x30c010807170108150108010504050c0919061e080d02060708040f0515060301060503030a0509100c0f0614070f020a0f0203100c08040521040315060b1602040c030b0607080705 77
    0x115000010480c400051280c5031040c07171200d0240c0c0c2c1e62550003050130395204807130180042d80404090111070402c80d100075409400f219850395012000f000d0302e01903071803a40c00030040b0b0071042401c0f44120030310034080f001000380034000e2800400110000c0e45a150042c030783c1003030106890015003803200c2044e501c2800b80e449800d41d90700e1004000d40c10800b020569890703000b5880c0407008621070500000700ea0380200c10f81c40707460425200d0340400c007100607111742141c10040700d661910005562400c4881c10640301c9c1c1e4001c21489460b07281c0d9401e080c0024244010801070030503180500d0b8000c40c045c030030203401c90100320f10b400450022070700d00b140c0780c0c0c0c2081c5414941240505159030040003240603c1c80784044c0c800c030a00d42d500d040f4081c4196401c0404510f801c000803c0000e00b42c0d4400b00003132510040102e00f50350380f41440c0b4038541000300140d07448011040c4080451600d8032442010440764202082803046c92008120749000b4003000610308107001440340d0030310004106800c0807132007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 86473436 1250 86472186 86472227
    0xb0a0b09041e0c020d0f0203041a07021f0206060a0b0403080d11030703140603150601050d091502090f0904050303071b06051e1005010e0616120905031b030c010807 72
    0x38841c042c24010701c0303012006001800742d41c004448040c8680b51030103001400340e00035030800d41003004801815154103c0740001c95020062200141c44030511450700b800c044c8c250040f541662840a4103040c8018800c0d44a112031001c05c4c0045240c21081d582500e42110481b03484200c401c08000080030707200308546404e02c01000300442c05034981c203ca00c040511106504040e02c50106141ea260700990700343c0004421040050071030b512070360140050f03512249002c594000291034009101d00141c00b440c07881074000540c0402400c21030740c079a81184055407980e805242c0760312a91348a00026082c0f034104034802c91000852000e0143c02000c194129004101da030415194008000e0f40c00c04240c0301e41c0c100070000401c2d490080d424001110010b03141e4215155243e0208030390303075002c42140c05220802c0f40070200403500118031101201c1c00c60b140c40b5641d44c141801c0526140c2045101c041c0c0c4a0680114441c1e6100071030404000c11007801d0035251a00c481c1001e407401e0003445004e24a682 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 86474686 1250 86473436 86473481
    0x1b0303230a0e2806030f05060a090506061308030405041d0d030f060302130603050114041218031506030501060801060602070302040b0402040b121e061008071814030609010b0a0b0904 80
    0x2074101d03407000b044490b030751401c01260701412a48002d1fa68102c8400d0b40c0f20840d22010030008186800031948048002d01240c548135800d0900422840a9000010f00c0d50020600b80f007981000e114000d9a0758801e80c00006110300055240e507034041c04031000040503150380e00c1c441103007110b81000c400745500400c5078a40440341e03001c04008140740c3c8000e40c1c10350709020961001c3c00200a2003402190001e001c0300004000c00004d840307002c40b406a000032125440c00020210b070000c450500243d0307165130042081072640c100b05003540c0b000c1d00100c040c0c1c1d2408c00108521500021007004072a4155000b045140440c1c00142c020700550f4059500c1600006080b031076100150041c0e031007040324451500d100002410b181c1600b44c0111800c44d000012605900d84d13450041c100c16030b00000c5071904003000c4d90341e482e0301a080b00c280d9025016410724643c82c118681b40a208440d400303140360000300860540040022488050351181c0f80c0220400a41102c0e180c66641000c558100350314003410014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 86475936 1250 86474686 86474749
    0x1060906080322031e030219050a05070504053303030a0801031403040e0f0a0b0301061701050115020c010c0309050901030f110102070501050a050c01091b0303230a0e 73
    0x3544100f1145142d2403140e80b140c02e502c0c54410f080c40c181ca411200042d403003044c04a8240a0b44c146000540a41c400c1c11403d44200c80c0c0314455502803449200a0304501c0f0441c80c08a00d44090394105901c241d00f001c0070032401c0ca0751403403004030f030341d020440804140d850614002d49900743c0d44011034160100041c1a500240c01c106640d0480b8400c00c500c0c00041d500340703040c03522070103207010380c0c3d070003103600c0b030100b200e810708a0042a0402c282d4440000d04000c07180c006400c40340240c0c44207015900045820488500a2140314018a45a00a14030304160321034029252104c40314040d05001848064900b4184240500005410040c04482c20755031203091040482c00c0090041358644002807066105500c0802c00341c04590043e1106e50401701807910035140354010318030403c904e6503a4070a140c0810030052070b00725014848488809102e04504005144e42c41034000f00350540c0620b040400720612003030895604030003a01c4c0c40407803801c4541c00240f0f01841c010f16280345410445400004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 86477186 1250 86475936 86475943
    0x100c031b052104030c05010c0201050d0e0f0d08010807030b0c0408060108011b020307150f0906050a0c090602160b13180e0606011701140301060810090209011202030d030e0106090608 80
    0x2a07682d0307601910303510346102e400190544035900000b800c480e0754200c100840d501a100e004609407050620302d04041030b07107029400b180c51521401507194440c041c1540e81c0e20080c4512039051700c20b850032014543c141f0480c0744c1d03142010700c00140000340d0b1a0004840d000c50320240e402804034a01500d00a580d00c80069000c0c0902e4003030540a0a41140040c26503400001140d02d885c0e84940142212601c940041c00184404010440950703203841243c40000c0e2644111740c4640341da40c00000e03400f6035100c2d0052487c40c10f500710030190360205c50515940003d44c0b092074202d40404200966031400030640300030000e156480030308080340c60009440b8149050308165480319000049907055516a03004664040350408050056072621005200304a42e1191804a400c006000810216502e64083d403400100e0603064800d00e03500d983e21011445c0c002010390062211071500100083e494001984524000c40140b0901d5558544c550205c4800e407c50b000400311410304011003a9150885501e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 86478436 1250 86477186 86477203
    0x509160507080a17070c11040903140a0804060b03010b0303030a111306020a03080a0213031104020910110111030411040b151c0608010905120a030f020d0209090601020c100c031b05 79
    0x1030784603e030300c000b17400c4920404020000e0b5400444d40c42014100300180b00080a100310700350100201546c0928840c40100024409440107a584000502d001d0620004607142c0005040c0b20f6410b000c04c11326965400000c1e282c2102d201c5400007403110842e0382d00e91040c03086000d10080750045843c0005c001e600402c0108115002c2d40f0340a0300b5075209803d2000b28821074615205a03803000905001003003150b510b04042034005003005191a074400c0000d9200404517503842e000a03111003228244041c207004a034410f03000092002d06606240e0b071940310380003550800c0d601850307944000110990300c0b501c1100301000007000096441a562100321992034014600a109604102e00010f014005114a05c00650080080e10881d410550303008160b9000c007005004164844241c2c51781c140c00341c401401200801c40005a64076845070a00203001c000030306007419504109991012600c0e80200c030281c08981d0700d440500d080711864195802414150180b0012001194150811200080f00300f03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 86479686 1250 86478436 86478467
    0xc0f0e01050d0533250f0f050c010608010501141002070b0403020603130c03080d15081c1e030b040c030c081602070801050903040f0b031303030c0507050f06040b0109060509160507080a 81
    0x442012000308195845081c160780c150001d0110300d52020000c4c4234a0140103011070110022441c1903039030113141e09590080e08540300c0c4590203c0380c1c1d0748a180c1500f1a000040450018020b01d82c54005010384038041d0f840060b006503800230004000381d005004403c4015031110b1001d000540300d08029043e80c101c0b41c415800e480c80c044411000f010010301c15011101020000c00c1c80b030040c4030703088140348802c0300c040042c0b2511403401c00390440d84a642c24010701141d9000688440d800081100b0394a07404845014581b03002440660190300108066005440302845032882804000807440c0c0300b4283d008114a52174401403241e901004001002104c240010302d0b1801a294820848144000d03102c0a80d1200000d07511b9001902070741220200300306c03d0030000d045c50800d490300c1e424603600ba8008100c0350483c7c000c11040100f0901d1290160225603410003800e4100400b184899501a209606407020000c540211600c076004690700b0542c0701800a0b1221910b140c0074002c18106030460 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 86480936 1250 86479686 86479741
    0x30c09040207121107030b0a111b0a051006050f12030c07090605040609021c1802130903080f1501050304020303040506120103050c010f080a05090a0c0f0e01050d0533 73
    0x1213400d801c00148501030300c2d0810340c810004e4070785900140092100764404800d58100b4400f11501ea101301c8141609294a6806400b103c5441e10f882c904010740d01c02c900001c40d240c284180216200c0c1f080e80361804409171079240301c541c2c0c1c1c01031180c070714000c290903000107200c0c0400108009034a030300040100c641c2560184103c9803110b080d24148d01503d8001d8806400171801129003d2854014a0f107002120040303400f1300c811500441c141c6050744101420f002d80b5019203a04042d800160203600c030903a880c80c0603ca0130215000810100034198040c100704020011506550f0240f00301c43c02002c0081c502540c0b4050114082d203d502d00344001d13030b11030280001015107540181c40300a03640310b050b61200c4040d51101c0103035000301009480b1380024820801608001001c003e07040b8090905288400181072800c0e04004500205800c0039001d04e81c01c0c07c0a0001032000101c3c20403c028082d0132440c5d80704000d500c05900c095000b05440207004140038403000803440610700007100d1a44051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 86482186 1250 86480936 86480957
    0xc04090e0f19080903031b060f0103050c1002070e10030b0a021804020d02070605041b0b0906070305030702160909030e0d0b07030e01150321021204060302030c0904020712 75
    0x101074507549001e030041d4160b00302aa9070020103407002c403401c0300c940c031071180d031400c1c031820300c0200e440d41e0061800c240e5156804901c84c4c0100204004450b4400c04d104000d40313103507055544250701c0b60001021507001d4011046c0c08250b4078020300241002d440d000d040d052151508031004100407403280320648801d05900003188540205000301c646070054084001c8178035204800303101c000d60100c021034080756428080710340011118080c9078015070059020580f00703000030000e90101c03110380d480070791440410880081540c9441e41035595a5425080540c0c50799103440050b0304210001040d2203c403a485000881c1e440fa142d80b0031140c05001e590350366840c4580e8000e102448400d4a4040c1c07511081c1400079108921980104514028010010801c65401882d0b101c1880c031503001220b80c000080410800c1100c1c19183c9113506209100600d2950f98203114443d441c4103601818042503000000107045400707013000c035103020308041c00840d41e985040c100058060a41c000400001c0c100c03492 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 86483436 1250 86482186 86482211
    0x30b0711060c13050306040606140d02010e09040507030203060103080a03150b120402010311120a05150a0915030b040b0603010f1509090c030602040f06020f0d1b0215030c0409 77
    0x35140300803824600502058540c80c11803050354200d0004660070f408102008121600c080c8002405240b044101203021800c202c81071b00702c0c40305030710b046000b020705d00c1842015070707805081c208000805641d113a5040d15642401d504103d05500043d40501c80c00bc0004204540c01e0014100350303a82e50b60401100481e040c100c51011700b684100440080b0034080e80c01301e0706207070f013451b508030748141070000c0d4020300e02121042c141c200c40a4071410b07103031103000c02c81041260301416a00c1030418a032038006404c14000590840b81038000c1309a0266a503e1982400c8100b02c0240007450301b00200440e41e00d414506034071070700d07022681c00d4000e508054031140000300c0c901a9445203154003a200040f142082400c000429a458007540c504401c5000040800c15070310042c4090890302e03040000050400390080d1030304444080080380ea6001810006550f903001d401c0c1d00341400071000c0901030540030b00014107107060061300081d54010000611400000c4c20340140211a0751001c140f220a43c0c000307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 86484686 1250 86483436 86483447
    0x901030201051209010f0c051b0712080304050f031204050c2d04020d021603021e0318210c0f010306080c0f031002030103030903140c010c020603060418050601030b07 73
    0x200003408100306000c480c1200c01c8100e503003139012480c41c0000912004c0828480281c5041c007494002051001507400c411014003004000741e000c1100042c20b03940c2c07800d00a4004007502c10f2024041d01e00200100c1c0c20041c00740100c0340d182610104403a100c80002c0d4000004020940701210988150b048141490510f001c280f0b011000c401c28881a045131024061203070060554040e50080e4200150524581c0341d20150921900c2d5207901d0000c02003a2501070302c0c190009403464500c014002220702516400421102c60014030401502c4c54508000072409010031314500d54100030403032404203581800000e441c8070b00c031002c480412543c02004019401c5400703d02402446c0c0d04480484416800d02182503400c42e500902100e0080d810510007100f01d800a0708200c000400d00c0008006004080201c407064003600b00c0681041040308001a245029904000b0b00907d40400081d520b075413143e205001890840078004980d400c40d14003151540307424081280c8030550180411816481803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 86485936 1250 86484686 86484689
    0x507080a060e27120304050d1b11010e01050d050f040302010c0302090d0609030c0f050309090a0b03060a0b0604050a0303030e011103010f03032d03150501020303090c010e12190b060901 81
    0x2011541001002d2908680100c5030680543c44c40340310426044510031000440c4503a000c0c2001c0e02441c020000c004040c42042400007c0308800c200510001c504030b0751050011180c242064030410541e4401a20a805498201600c107450328080052100c0740042d6503109500c83c0e0b000304000ca001503000d800b24000d0594143d00500307041941000101c0a0784144106400703800d024840000ba079403400703000d00052004980c00c0e0404a40781070242072201046810411101050100540d40c0c07020941d28803009000503241502d40c00400b4440c2c03a94801c0381c014210140c0000482510780c140600038100001ca051403a62815030b03140320109542040da03058601010039102028a035850885803140801862002020030b4080d582c8c01010081d120650028141c401041d1600c0c4484654a0311032168402c0e81550420020080710310004145a03c0c00306003400d000c0c44a80714a400300d04140d68401c0414042d114840da600702c100f0b80c0403229840280b19449d45242c41e40d4040c10b001e00084203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 86487186 1250 86485936 86485951
    0x5060a0507060209040f050907030c080c060a0f030b060c0309090f0402061c020d1401050306070c05071707030203030c010b0a120308010504090201030e0a0b090f03031006050f0d0507080a060e 84
    0x707001400002e0344540040c01050f000600c0402c0d000c041c280c40d0822620241e40540441d030100904104001c45051180000d008003000760003410044800b05280380300350901041000700003000251807a0082c0c0c0031400c0c0c001d001c3c102c41d44403021601c08036600e60201d0080341c0308899100000d849074160543e0741d44a103902910362070410f000190070b15180c405400e08240015028030042407000582d2043d4110514585400c8000d549800705040c1403400c0503040c1c00c100401171441c01d001c03420029401c000c65000c0002c80b8010211403450500f07100844e00001e6050000042d500000e24054015403c000011030354891800d40e506402c06100c0d40d00c20780180410b140500404c1a46010350001300d0310b6006050128003156080041410070603104401c507400c0c0000300c24810b03201401c0000140c00d180000045d4a18104101d0064540302c00344200c90400c00009030500c0c03c070748100709840504804000038481810401005010084121400043c1c01d15003a0700180b10f2240c4003103540203900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 86488436 1250 86487186 86487197
    0x1d060604030f0f0f0809011b1a060102070e0c090406050d0b15010e09071205060a0f0b0f1b010e0c0901030312050c090307080606040c1707300c020705060a 68
    0x51a0740346051040b050005031032604041c16000040b4880c28154084e103413044501c140c0e00d103001800902400c1340300d10382d980090320810403600054039023044c40d244090544c40118441d80c030100100d16203c42070b00701030341d1050141e06104c110b40b080d02c0034123031810f0200e40c203000d0a40c44400b800301592502402508801c81070f4007088da0000300487c9107580d0507040c03402c0c0e80000440c1c40030540c0408252070304070008064401c7c00070400414450365030080400c42d42c02403641c0c0307090100401d000c0640030f0340c1d1110314001001121110044121001100d03c0c010608030036513201c07242070003050820141c454a014443d0f480c041443d00c4103c0a040c3c950640b1b910050142e6540e80b00d00400c0010030031440c201d8100000f080744d030790800c400c0000f48003610041c015450200244026074224410440a116540c0300b0a0302c102011881c180d4481d159241620500b0342d40d00c051014041c00c14160700d2044400002c10711248601c4e04a03500004442d02214032095898050103060710502407018001030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 86489686 1250 86488436 86488439
    0x140402010206010905220b0708010906050d020f040b0910031401021c02070c0f08010911030c0109170109022e0206060306070309020607080d02070b07022b0c0b01030308011d060604 79
    0x304035505c0150840e10703050350342c0804500c01d8190003080c40400c0050341c2140c020300800100517032042c861409454200401e0000c031313141901107200c03d04002d81c024422800b0307415048031500c842e80420500840180703500c03070754102103120612420440c0801c0c0c0320340b1501c02e00e02602103814004c5074115507400d044800c0c07000200106c1c800a4018039400c50307001015030000a1030038901200503024088041c00007034001034600c0c280882c3c80703204100c50b000ba044001000300c41c0c2e82060018044501c2c8800514910141d0701146004080c03030800254000c2507512011210407100c012100810451000c40b00001303207225003680c1c0c80c80f08070355465141d4084800900300a209801c90070703003144050030160400c84aa62442070541050104514852740400c841c07092200700b0107100e400c0001ca0020b00309204400101c50030f52082c031070707a8030343c94095202c0e007000d800d01c01c0c1c3c200344481d03802001348422542c4030f03d8000c6c29850284100c04d000d41070b10303045444c580c1255228501400008180380d1400307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 86490936 1250 86489686 86489699
    0x203180f030a0204050f1006090e06060f0d06030c0314010b0d0212010617010b0a0f03120311040306021c0c09240207050a08030a0201050c0a4d0114040201020601 71
    0x40c40104000e070140640012240161964040d05000c2c3e00410307202c0000e450b001824402e2000568018030401001300010080b030f24840020320340250003611403e82e5840c17030001c007000d030388220303903180d82044c1c9000c00c00400e1040e006414416a4481c5d03841140c5404011529801d95030b041c4a00ea030710100401c1c184005113410442c0801103144800082111940c42044011484c1080e06007642c0d651500c00074140c030701c1d14418403c064601d814002c50308500b1521500d03001c0e11028000020700d03940b400345000e940c0505081e07800a55111200791340e10742d0303030031052101c4510a1102d0b224060400000020041c010004601034825082c0c02a000e40b0401601004503614110400298000c28401082a80301d914440015000c180f00071a56000004802800c4503402414499070381d0b0b0500440d000540d00030031000015905594105003515201844980c03042000744d00c0c560714020025460080344025444003002c49010020880f11174a0094010416000c640c0240141c0203000184000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 86492186 1250 86490936 86490949
    0x9051603060b1203121503030c0a0b1303050a080c070206070303090b061c1104020405090907080607180302220507031d06010302010f0c1712010816060e010c0201120f050103050d020318 81
    0x804060900044446c8001010038115070115010701c649130040e5060f98284804141103580140c00c411901041c0c0b00b980d28020098000c0e10302100c00c21000740d0204208085040540c0d581c1500144520ba40e41140d00e17000d4004d0040380c07011140101200e000403078500c1c02d180640c1410310b5841c40c00a60f01a20b0790307030b55039a0b080c00d2050b41d03010ba07080c40085100e4554080c0141700b03010280c0117144446c100b0f10441d280c072400501001c1040071205004401101000750107080744c2d81aa8110a80345403944d0800e950b20400940592441c40c00b000c00a24680c1a0002c941849410070700c1c45400c46603a8102d510b4030002d000217404500d064200d02c505512940100b0b0b00c19000c1c050096000481740b4145040307901401456962254080050003c04003d01c400040510406001414030b840d00b04040d00c51400180c1e117a041c0151940850150f900813040c405081d640751504201e00b00c5007000700d10040100780400d403140c0c400c111044c03c000380001b003140d1800395181c01c044058001c07101000720 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 86493436 1250 86492186 86492191
    0x9090c0306030602030f011809120807230318070509040b041a04050606130b01090b0c010204090e071a030c030103110418030306031209030804030b090109051603060b120312 76
    0x4040d03035400c1c000301150300c5102440c0203c1c603858000500e545007100500d1058081040710010910780f04003c4006418200010140d20250410202c682c4d10044184c0c1c10405070025803441c0701107a501080300309490340c0118460301050300d44082d180c0c503249030190b0307070451401000d401c0b02080010501140300014095032241c415954044c2003103030016417840488041c0c400300c420f54032070b60a21525103030400c110320700603240741010400c1141d1000000c01c51352640c440c5000700343c00042d142c4101c00082d0100e5001c0c00045805002407554501a23381e1200030b031150260789040350421a1007001040100d81c011600030401c03c0c2140d0070350710703003000c80d8030a1446942d10913900c0130940b642c181604c1079204103d0090310000f60711841c1d820b08043c454265614581004010b0304d0500004031004283c81c06e6030b8009c1001d00e01d036662409194010000714101808a01c112801e814002040c01c9180003600e10a0a040c001a00100140401050b240c03032403a032182c0040c0700f8450303001002240302c1d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 86494686 1250 86493436 86493461
    0xc29060402070c080a0f0b060d11040b130c0e131401060f0203120414060a051303031805060c0403060b090402010509120c0402030c04080f0309011e0e0301050c0d050a0c0909 76
    0x7403c041d42e0350071042c5030000c503180844240701d0104211050008070740c00541c0c44035085d10f03a9441980d003a9a07589001b40d2203107085205554802301d2031070545405080c078240782001c2130308002c003045003280a010740307803d482213601c200b01d11000c140e01111b0500501208034503451201030300707900707040041d0f1720019418802c204500c82840403ca0f2000c401e402507014a00891007802101103000710b480c02c4c04d07001070240218505017410701a01c0c0c070600c241400c0700c0360076240009010441c042c8054034404d586e41d01a1007071099100b40000d4003c000b000300212071003800d080101c005140c0c24030035440c0e4200c0d0040d02044041c0b0900d842820240341380c540c51640002924100302103400020300700d03002650100250540443c0031b010b001000c000e451101500600150704185c039000000300802c210000010a91901810340c0160b0742c044c01400d80e20150081c02440b40f49880101139103035801c92038074061418200008200c3c2600c00d03100d4281220020341d21080c3c502e0030300d01b00002915501c3c1035207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 86495936 1250 86494686 86494703
    0x110a030f0210140f090127120f0803090105160f0f122901020c0d170a110d020105040b060d020306070e06070804030c03020411040b0301090506040e0d0c2906040207 72
    0xc02c1e5203030004000c013807a40b4403c9a15075036640d000506040d40c255071503401d0704000070302d40d42d00a1441d44000444514505862102100e440e0010031340b008000003c10000c800b100b4400344c504103400c954841d81308401031813001700303100104035403591300720440c24045100c140c105100c1e50321071003010560103040c00300460450151450501c1100c0010100f1041c14082900400c00e0340c0e040c081d50a248004580c3e1030301d1408a03803154400c1840f440c4241286140c00902018094000c00300004c4007070b00c0400780c50401d00381000107406442c0c03c403821140d10722280009600ea21302016003028558019000b08040c7d550510155071301e2081042440d8854030500c20040000c00d100010070185104480910314185184103100542c0d59210003280c00a4041c44248002040c9006590445041c0e030000301d01a2250004140202183c06145a080c0600401b4000e815040030904554601c40e401c0100c55541071b01081007640c000340702103c0c2d40c1d00c00c240414064074094000d040101d000c0c0310308 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 86497186 1250 86495936 86495957
    0xc07081c18050a290c0d060302090403080103020a0501030501080d120b12100b0105030903120a0f0603051b03120901030e0715120b0a03080703030518010216110a030f0210 75
    0x22010884200310702194654011010103041004c034a00a07076140413a12030b10429400880b4184280301c0b0001e2070f034910070001040e015010005600000c004580203011502c0c0c5040030705000b01610000d0005a000301440000001c0715440780c41454100d4850344007400200d141c071034080301c41400d682d40d40412991245162041981c2d94000740c22882c0010000707009440941c40b40720146ca00c17103203136141440402e208102075604040700f2a41c180202c02d044800941d42c0c0c810b40002031000a000304061071505401000304400080d14001c5e18500003484256841100308241d5140040c0990480c844c034248605c0800754000c0c6c020300c01400c1d120302915240e07034a507035548009040c90ba01c9071000603200c4518a1581c0030394481c3c4542e41c401030341d0200d865815501d8108061059000040800d0b985500281040702840103001c8584a40130096542d6042002c00c0d40740700c0c1d07003400103451000015100494500c0c00100e40e004407544004d4403662000305400b084203030310280490f1414000710009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 86498436 1250 86497186 86497211
    0x2070c03120e04050105030f0d05031f15110105190b03030d05040516170a11281805060307300b010f0e2401030b04021206090c07081c 59
    0x41a540720010380e51800180ba80b80000c000584406910840c043d400034000d030802c400b070100301041c1e01c070701c80e00f420380c0c0c1c0751111180604148172503088502c03550509000410810a0550700181095613640c8132035042c1420444a0b00703c0702d00740c81c216101440204007034151040d030342003100b203280c00a00743c90808602091807415180308940485454105950050600700064003800140150b1402541d10b040600c000554890a60300e001e80240c80e203007070070b0b501d40c0c0d140c0f001e0f0310340000780004800c0060340c031107001c0c0aa642c450242000b0280e5208005000a40d81d00c5800d100301001001000e4240c074003007140681442e1000c070032115001e91141d0030036200e00c0c8503184622074400c3c00c00012561502d110400380325010b03080340c1c191003d044248821407803107001d80082c9444402c0c0d24102c0b07504000c01640145124000b071074020380045601c9110a101c0c11069210b003106035a040104d0740c0c2c00641040d00e100e480c1006110300401c0c000484115001b100c562a401c07029840060741300542d69 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 86499686 1250 86498436 86498453
    0x616140708030c0909010b030c09091018060303020c01051c0207050c060c060a06120503030610020309130e0705010201020408071202040609020d1b08060f011b0c060203031e0c0d02070c03 82
    0x2504008107240014501300c490500080f0342d401818a2030496040d4104410500018450007692500c540a0346010502034171140811000a142c81440e6119101e14021883d015000620055016001d10500d501003540074038115000100c0302c024400305a040710300008025005003000380c3d5030b88250072408901c0e032150320051410340c41840040c60030346002800c0c070050b01e0350740d0421104407031a20079020001e5000803d0300c2e04000c046a032440072a800b01c0e0300700c0c91070040d03034045544441c52010030001191180d100b6124048240d09407000d141d00d0f80c00681c00d078803c6104440e101d50108070100020b000b04030b45698501d00c02000800d8450340e40c403003c0103980103444045641035948681c09400d0a500c84000c3d00d00140b0f0501541515185000500b03103000320501506101e40090142000b007501d00d07249144036803000400c4826522900003d64130341084980040d040404511403401001c008810351188104091030792402204405240294002c400122041c01c15940c004c0300040c07a80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 86500936 1250 86499686 86499691
    0xa031b0b040f0f0906030206041202040f0f09020a05030a02091611031c0c090305060106050c03130806060a060302030c09060d0b030f03180f06030a0c0525060e061614070803 76
    0x81c00007440b01d08041485905040b542c3c400246030b490300100300016165101170310200e0340c084003961900b40590000c1381c06410303070f0b60ba00e40c801c03442c00345107210f10590303903000320f80c0300e030003602e0f1800016207403000d06503106182c0601942c0404104d00090f8a084807400455200d00c2500d8203500d5002a103d00c0ad10307503041494010011050441a81c1c80800c0c584152038544034545080c0d5201840c3d91a4552104e5042c0111007c203c0005240440101c0400031141511190307440d41d1001c2c2d40d02c00c580c40d180c00d402e44010380701e0b400c41100014540d1080c001e69001b071611140c11890010701e00c0400c003455003c1200812041c0c0c0301d110248169400313000c0001c6101040f8041d56480d5801c0b8180050f0000c81480c01e4802e510050402c00c8079102e00081e2907001d00185800100107600c586c0136900c600036400007500507001e44041d40c5040780c6001841492920680061201e40082e540c51912940110b84008200512858402c802840340140c04458280b200c0e105140c000c580d201d4500341c1d03204 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 86502186 1250 86500936 86500949
    0xb0d050307080d0b10091401090f0e0103030201050f0c030621060412020609010e07050402030606040b030a0b01200d120e070b03040507050a080d030b0f0a12020901050901050a031b0b04 81
    0x303d8800c102c14860300901a468004640560116101c00c80107005030303115010380c001c00c1c0035001c4c091100d42d0040d09004058603a009070440c0c525905e00300c18000d80e03000d0104400650818011401c11114144074a024a03a041c010034195903c5e0402d0101144840304030820800c10a0000d440c1e944003485035900588c052020507080340182c02001e0b1070000003419014080c2c3c504209801c4a40010402c28280d8170304035005a41c2c0e443d204005540703070250b0b40080d01502400421300010380005d900a256801c0b003a00d40b209400d00450305240f03a50b911641140d2503400041c00a05000d00c03c3c040701c0301d900105c6800040038a8401c8407a80303402c02503000303642550000000d0100740042003150400610044602400305410101000d44910f60b45c00c80b0000d041e00c40024429a40d00d00103d00b070342201c0036201c0c21100d6a0384000c1500e207041003009a01403013106001081900304011014144e40300901b808001d14035594440c0c40c61400503005c421034441c082004a8100180b42c003c0005020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 86503436 1250 86502186 86502203
    0x14031303080d020712031b1407060e03040503030a020a0302070506040e0406093e09070516030c080310060e0909071503020403061b09060905010210020c0102092d0109030b0a0b0d050307 81
    0x5130266807d000e1111050501c1c14058030308421303003100c104a811903000980c81403010801c0da0b030740114141340d40a56000680d040c0804584c03c00d0b941c0d4001a0510403074040d500303c038505540c45080c05402c0c031a03405030381082c20904000601041e800d401000c2c0d5248220700340c14980d10a5001c41c200b039415800c00cc940074031501402e803000c1c1510f503000d406008040341d941e0400e0401d01ca01030500d2181d854906111404003812400b41801105801740d05034007e8556070b41d82c41c0440f03903041001078500503000458210010b0161504190b1005d0b841202460010100c0c01d08210344c980c0d4410000001030101030b0204008000188039001388158001315051010503003091042c054001a55034005104100454a04106036a40000d1007209540c03d0200160303240c3c20cd00c640e80c060f00c80c001d0303c40d0b04011000b2080000e941320560800c02c60140141107940261510b004413640d2000d0701c00900388890b140f01142003440c05030b000007181000107102c5090400e403962540c1c1546c22500c800d036030948 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 86504686 1250 86503436 86503451
    0x30e0a0b090f01060509090303010306090201020a1217130515130203030c0a0b0601050c06010311041d0c0f01031a120109170901020c090403020a03080a0b040f060314031303080d02071203 82
    0xe8240100d4018050481b007030f84162805d0449640e03a80014403018140b0350302c43c40c1038410759000b0b010800b4a19005184800e070f5021902d8090004104104500071541a40000a208a040e942d60300d1000d6030000141c00710040f15030600010000c041d20301b150b031102032030404d80140d604000420007910300c0d0010381a603800e9410501040700004001d981442400c1101e46800c50340401c200e410360f40d0021442c10a0070320003000c07030001c10a4082b050700c500c1310200d00203010a40000c248901c10001c4400091900910f4011400ea03000099102034614503009050194540400790f545401d102100015040c41d4036240c04070800c02220020700e078001c000443e0805940e0520845001c83e1064946081c107003816540250307550b20b140700240400981d0000f0407101e9a80d07030408041d1003001002842035a12691419000f0b003058132007112106c1e500e2801d00340500010003650202100c08034600842d034a0364541205c1948200032000e01c942c0e0802c40c03480061400ca13007142510849a0700001c540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 86505936 1250 86504686 86504713
    0xf030b1512060c0c011b020606030609011e0f02090409080a1701060c11030a05060c04050103050a0e0d121e1b030b0f040b0a0b041203080117030703030e0a0b09 70
    0x14418040c40340601184181020705400c0041c4458020303500406150759940300d099914010800d5080110161401c0f0440138503055000401da40903607000c6060b110113448055000d03080310401e207801d00d9903d070402a8682c1c61441c0703600282a26130b03600e10242c40e006181d00010221280359604880800000c41c00f00d01c030680c1701c0c500710440400305c00c1e000074550400d0000382c00c0184105004203002001403400c20640c600340003422a00752f126080320020304140d0300f11b8140e50000c0c0251070000b45440c0000b0f0700b64255001d081c454807a50400740680121101e401c0740c00540883c00101403680300c03c0c00502c0d2100c5402e42641d60280003200091106544480652481500d182038040504004031b5240c00c1da990b0414482c400d900315400030310040c00340d002c20101c2c011a4003030222060007040c0091000404015580b4040c42642da45503540c1c5c944104c120707801c103609819036441c0e100344900000a8026803019111188480440c0c00d401d84542d65001e4044041719190040d03084018005103c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 86507186 1250 86505936 86505961
    0xc030503130b1222020909030406020c031b0108070917060103030306060305040b180f0601080c010905030d090308070606230406051c170f070b07090605040501120509070f030b 77
    0x1800300c035207015203007890091083d07880ca440604805001d2590461a00356021411004410281c0c046c1c1002c00034a0110100e07030300c94110340300300e1002d4041c17504806d419103404200503c0c2e4019150083e2180462040110384004004040c038090016107e00401c0d10201150b50100901c0b0840c018140c540c1540b034000d007541c2c45c5034044400c0c94141020320000450f5040219400041501110000c0142c2c1d4072480c502a800640310009000309400440d1002021440100202c0c2c01e0300d552548075130714010300d03a41d81c9503801c43c0c0c40011090401400002d02c04002409100d0180c880400c4032512a0011003080d469180d42d040e44000c0d104480c4011300f060f00403003009020440320401036100085200b04011103820006000c441c00c900d04c141c60500b41c1c015520103680300080141c5030826883c18102d1010162030480c0402d040c0440010030708e110760112015507a0607510110008500300e9404040c1c031016007020001c0c064018041a6010304000c21401180604120412400e280800002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 86508436 1250 86507186 86507189
    0x1090b01091d07031515020601031109040203190503040e0c0a03060608060105070807021807050309010b0303030c12070c150207060e03090609060a0e09010e04020f0f091605070c03050313 82
    0x10b4007107580d0b40c801000d0142c0203105030f00140904010504161444114840751400d41103262103074245401c20b0b01d001c0d80040c0c024140c0b441208000301c0110382d42d00f0051400380840f0002e600d030380076640101c1503140b20100c070403420b441a02201d0800361140385181d1444001c4800c6001c02d40085514115240e141c003411300100417a0601018900340703100003e0403881200400341c410200060f2800c11515054546064120300460b210100d04001c0c1c0020030541c0103a680b0416582040248000380c5400700441e8019200182824900850602340e80c1c941d600044c03001d0188012046241302050b401d5000054500b0340d075000507594682841c3c00320880b80003400715141540140250119512800c0458040c0341c030807600c0549030303d04107800b201c10703032010a062038100e030000740009642e080c4541d07004e0040303100b182c408601c090b5001c10301c041c039511400e0055004d411880441d562510500c6407400071030310340c83c01300e19100c100e4588980825041c1c0c0f0898941d800014107220420003458500d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 86509686 1250 86508436 86508449
    0x408030414040b09160c1401020f030615092b05060901020904060801110409020705100e010902010e01020604030e10020c09090c010212160b0a020910020706030b0a0b040905070302070b01090b0109 86
    0x780e40d0900601718801d441d0510010340a120f80e8001d00b0080c088411010541c0c002100000e560351280c04901102c10f0304180c0d5500c0c0641c804101d0112002a40c4060700c400c103801408918280110710a034410121a05a40010aa40b070800720b0700412028401d080c13140f9241070000d82d40e40301e0107003070000b21009a406a01680d1500c00005100241c040c100e41c102d688250002d80c68007a2410f0450a00022a40800440f450700c2d880d0400d808040d00008e1089000341c0310f03034421100000041e611042d08a80040c005151821054114a0b041d0510582050a841210140701c0c214010580d95501619202d0543e84000104482c543e410450300d1030075800221080c0c1001d0082c441e1030300000c06260002c00c590407550004030f14501d01c1d07042e90110800107042a0042c080d042020b0346520302d038001e000000342006101499070902103602800c40300c2001c03040b80b40a14007442c01004000240030307041010380802c03a00010441100701c6501900c0e69074000911090740c44c0002d0070400007030784400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 86510792 1106 86509686 86509699
    0x1209050d0b0a0c05040503030702150408030f070615060c11041b0519090f051203090604180c030b010504091a030709061701020f0403020d080408030414040b 69
    0x18091894601c2c1080141000318003201c0c03611690050b960941d004115042c01424141c0244625050210146051603140c1c50114103591180c0d4140349010f0011550300d044c4040c0e07200d01c03900d0003005014294000c1c0340c808080d1260f0f01460016105c00804880c1001544442d04000c104c0104000400c0c05149164400b821a0300720703401c00002d005113680c0d0345000394010359200341914200a803d0042c14a840200300030300700d05441954141c003041c86290702e40d80314000904050810304440310722003000031202d80200d441c604041c500301030801d00351900d01d90304a01164143d8072981004684100003881002511500e442c21542522510000069281e2150310a1050361401c9002842c01070803000d02c10300341e01412100410350882040704000620f803001000031824414100a0308250355111000c0c1540c00590203007208900c640101200341c07415101d43c60115000322480c = true := by decide +kernel

theorem cover : BRFrame.Cov 86330936 86510792 := by
  have h0 := BRFrame.cov_init 86330936
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86330936 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 86330936 ≤ n) (h2 : n < 86510792) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
