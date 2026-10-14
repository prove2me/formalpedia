-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0569
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:29:53.077245+00:00
-- url     : https://prove2.me/submissions/1fde8d11-0362-421b-a477-26d9afb9876a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 102158273 ≤ n < 102338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 102159523 1250 102158273 102158311
    0x30c0d030e2e0f12020315010908010903021507090f03050f0d0801080606100302120a1e0603020102120306030705101805040b010c0f08090a0306020304020406080604030f140d06030308 81
    0x40310706051509016060182c2450400c2c00c800c840801d44001c0402c200b00401c0d400b603000c8180c90016602408481a01a503240b035507030001402d40e1051380c421180d980c1005044008030b5008604c0e5001034000d88035100c4a940c0d0131005503110b00c40c40e4005421040302d0100002409004a00361403400084401e072000647c000344121030241d0f00780241074030754106401007403807841d10f17560085c0303e28000d060141c10072413140841c1c600c01000320741068406e42c8400706100c002c420104084803150080404100c03c0c0d007940c00003541c8140f000001000c5010000200f1030580e0304001c1c100c0100802405480340c002052001420280419844d1075290131003180403075540b902d4000d54902c824103035140c41158665480c4c04900d0f200e280340684280904100c0f1488036110300d46403801850103258056628142441444200e840e5588032403410f803c90b20900c00003a90116180405054a14041750b6034084464024582e1013969a107414075403619000004140e08900203600c201310406070f00840310b107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 102160773 1250 102159523 102159559
    0x60a02061e0727150f0e03030a0f080408090a060c05010506030703030f050a17010f0512030f0712030b04020a031406010807080117031b06041502090609040506030c0d030e 75
    0x405603024000f1404096070b0081c1c2c040526214185080c240c40c00d0038940e90346240441009034071240150000b4220007948140750781282c1c0c0e941c03c00c441030300214039150b000c2ca801040303000080300031002c1150b50f0000c181071116403020340b040307800b00800341008030780c0e02c2801400000340f610044860307500713040014a461901150070350450ba01602c1d007090140c2030182c116080c1e0700c011840307414044240d003604140100e52010314043c01d405281e0700c3c0e00605180c1000b491110310381210410703520070055685207580400c10b442003660700040f40500079880d6034003078000d4141c4070402508a880414041002641508006440400801968181c1d03c1351401103480070011621040801d4015004000d001d1704000c030700050382403400690b070502c80c41c4554100f41c01041f1030302c118564000e00c04d00c000d02c601c01c99901103007031815800b180b4207643c0f280400c1c440d003d140b003014803456a420004c0d0042c1c80600210079118001000b6542c01a2075160250010a16400c1d141c012740d01d04465028441c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 102162023 1250 102160773 102160831
    0xc090f15150806060c01090b0106080a11040b07030f11100203010302120105040f020609040908030108010e12031302010309060f180c050d02030303061009030b0103030504050324040b0403030b060a0206 88
    0x4681e14002c0310756418040c00140d61080306641465035964085070080348412412a001e82920b40c1c403103206060510180c400d45170b000e0120406d0200410040290118071000c4414a42c0d06003822500a101c028054521150980c05050365005950b110140241158001c50683e40300b00d42030141c140183c41c0d49422200c00712401801c14142540c118090b181a0003c0d00c3c1a04005201080300345541c0e4400c0300380c0e00207038031100c00342c0c0d1034028000b1802c6060125203c144c3c1d08008440c01e500c0c1886010b001ca00300341c0d0b0040c0c140b541d94806942406032a0f045800c030340e014914140b20300340340c0c540b50708104101c0311419103068013806070105030340ca0507452510b94160000e004600710303208c0741e04100c40166684000c6080c0310700349000000003102c04801c02c1c0218003c1d120b6944407460101810704101c40404001c040d29010b0b00964090800085101e0f04a904058807400c0d82d44c941c0340550052645040d030307a03070000340421481d246c2d590001e07103640700d04501200c0351380f000552a0003804d04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 102163273 1250 102162023 102162059
    0x2071721030601021e1504021c080d0b030c0306011811070f0c090506060f090a05040e03040e1012110f060d0e01060e090a1e061a10020601030b060d0c090f15 69
    0x10390400ca218020b44400b00411b241c009000030300150701f4400030720000200c0e0800903011603e54801141c80f5051f19441d100d000e0303223044240c02900b20460007100007511404140595011a200718815104001103907009410900e0306440c40c40c4d681d0f83c541062840a00c00900c01c0f00c40d0b40c1285008151038646000350740c094280a0441030a06d41103195000c25500041071007908001071010001e6680d95500424000003243c1d8041c0d07070349030b003005501802400010140607056000003810050078128103200c07822541c0106d02c2d0301c2411031100000301c000034040601a44940c002c14520a4020641d0000c50380c0311105008002c0b6580e01e18945040f01c40c02c952101741900316120b450041521f48600034030101c08031089900c0c030383c2c1c03d549000440c0e1210500e1066101c0b0051008094180025904440c03e90743c00180a590303d16034545211100040c00180102c4100c054903040001446444000c0c184080050045100e092800b03001001e080142110742d010181c000902000d00103441289 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 102164523 1250 102163273 102163333
    0x51201030c0e16081b210103140c10030c020c0901061e08040c0b090102030f04090c080702031603200a051b060f04091805030a08040b06010f0207172103060102 70
    0x813a07594400d0004030b0212200003200d0440b0700300040c80e64818182038502c9454080e007408907580d410760400390084a40c0c03021800c590380c8200744000c240d0340e4a54918990303180c0d41c0b802150408491200700d04015030300c001d040c0c000703104000101c2c8054128452008244840003640304141040b02d0886841c502510003070003210f5800307418845244000c00800000c070060048910340015400312044660041c0e110108440e6201100c56009501000c0c898004946100071030900200c1d442382d02625076041c0c001030a01414101c0d0b020000384003207150a049400c0e4040c0c0741012494100300c0d031654000c0840319000030031185c1218091500304140c902d000852400141003e04042c0814014404054000f111000c035003025000a00204002c011290307281c1d85094082c1018501801d5130880982158144074207030f032010360055030002c0c5d008101da000c2881c8101080040c10303000e0420485076102c40480d2000b14080c851078130300324000d502956080e0300326040c0c4c030443d005000c1a005c4040c85c00392 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 102165773 1250 102164523 102164537
    0xe0d08040609060e0303040609050c090106080612070503030f04140d0b0a0b061b0a0201080604020f07080708070c06020609060f041101030905010b03032b060308030f0403051201030c0e16 82
    0x10950503440071452501c00e43e00002c0f1045801c03000e81c0b542d0000c03103040300c0c4aa00c0d181c3c080100310782030104498005040e5010800303075040031800383c0020002403045004d403201d180c0402042008001c0d03030f0004e11f40076095039645c012000c00d480c0c043e4002c2c001c0081a81c511100b020b05410191711120340d03542c00109442c40c035110b40701e0002c00f0700908004198004400d002c038414150500a400c0503102d103070001071000050701d00c00036205100080c5118400c620600c04103540009260888030480c0c0e000250507907540c51441e118400303010f006001f5007280350702a408158141c0004609016010100842d04a60303148400d40c249950101c80091145507811120035881d4041d820050040e40700e000041030341003180380803170320715040341045806c2d0341d40484984802001102030380300c88042c180702c2072102a0a43d01c40d50124440034201d103c2200181000a06241c42076090321118035400c006034541d944d49083c801d003a00424040c490b44a0710740c9000c54030308040d0700803005c070404994071070b00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 102167023 1250 102165773 102165781
    0x3070509010332070f061805010f03112701020f160306110d090b15030a0206070803100905040b06042403021002100e0303091903170411030d020d02010e0d08 69
    0x540307201a07a9500c03c0b1000c90b001c0b401005000300780440d0000e0140398811005041c80d24030010004401407030480400140c400d814081642d01501c5620000a54100814101e40c8001002e600d4030444003c0c03892901c0c04061010880980005403032852030903800c9801a0040d018903e032140c1000043c030321410300d421020400510a504040c41c0e106001460790f01b007075039100d8010203030b90290340c0844440ca442c06c01c101942e100a102c0d9000450185d00800c01c1400e241d001c076240388107284010f8030404c00800000c1440f0703505010100504a4100b05000e9030619241144007280c042d950a48030303a0400c080035a40813200c1c40c05031110445c04450601452868081c0103007031a544129000b18010b12030891425591400b450a4260507000116660b2800601c45400c1510551080a400703d6823210200400c0d4081c11081c1b1040e01d4682e41440c80c1c6640c500040f4071aa01d81000d901809841c001e000e0043e00416490b000300341640003807101e903070b248490a4451844402200204142d08046 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 102168273 1250 102167023 102167063
    0x20405032109300106080f0c0a0b0306040b03190606060c1203090201050f040f03020f030d1409011b1109160212070212010e060421080604090201090b0a030209030705090103 76
    0x48841d464030340302c03071400c0f50382d8288402c1c5040055a14919560303448000401c005413082006066110b015009000130400d03032800540c101c2c0d1a031007240300407980440810420350702d552002c20507640080c01c0b182e00c0612220b0350340c417000c03810f20705485041c90214002a181c0c0182d81d0304282903441011201e010408400c168010301440c40241e04121052201c10f51680c4464001c2000d080401c202c000210318510421010b001c80c3c5801c14041e0704030036403506000b07400a002d0082800c1e10485540c44940c2c020042b01c80c44034036a6100c1c80500c84040500034006c0200c601c4c80070b10020307280380f1515500d02e900c09420754031036034003400164465904000b40e031101c2c00140040b144014080f207540740e642c40f0b0302400d442e46603021900603080807081c8020000d002d840350b8a1846151100d040f00d80c102c600183c807c90303008185501513a2a020244116803182a06001810a03003003200d40b100c5100ca4010020f402082400c0c2c064450310754041220f10b451030809040766031142c41c40c4101c500e00006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 102169523 1250 102168273 102168289
    0xa0518090c070203060a020702010206040f0f0b010e0105010e0a06021906090b040b0105030d0201060509040305160614010504150503060414030f03090a120c0506180c04020d020405032109 82
    0x1212448804190212000e544030040540211030444080da2120418010581400c0002d80210f114034410840200141d0b001315041e5445504040790320744403801c034203108179405d414001c0200f00c10a06000801c0c81e00b600c500248c16039000ba80c071039142a51600c1845501032141c000e800c0580c1c450390217003590402e11703010742c0b074000c1c03064002107101c0040ba6a00c10b400303103040e136086841000c9040140300c1c0342070401c1880c1c03000005100a01c056464130010404c841e80242c4050704000c000180c5410031244680d481c0f450552081d0100206034044c41c0c4643d019000f030054921030342c01d02c6e0709404415921b900002c152040200a84295199071b0340c2e402403c00c0c4070403d440603000601a592002021720051071091140d640904080d080b0783c40d08000b00f00303002c40e54206220711a10000c0114900142140e030045281580c15400020740d0702c0300b4030781200e0072000c80e8002d000080c2c00041451075000f500031030300207504480f08810000d01260352004500311403445520b0034000f5221a02e40003403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 102170773 1250 102169523 102169537
    0x108160c0807060903030b15040302010c0827030d020d02031215090a050609010b070b0402041d0f0304030b01060e1309080d0c08040c06030b0f1201060b040609290a05 73
    0xe1144103030055a40d10011078014410554480d940d80c0303c410107068040c0511034680e4070446810303040c07090003104551540501e0001904002690000744100a104000c5902c401d000501c06c40c2d0310214004429660000002c00c18064001c80c03003110303085400090409007109042c0c000d98248046c0308950808424000d04104108650740300c111200d0312010304003030040c034110340c010516240030b100780810b4001c182d021101d4000c0800000c0c011401028005800c03940c1210040f601000300d1004045d032012541294000780a0308011012500d00080104101c3c0d2140d94410b91503070740c7c0c071000d0310b508140741c4080703810821505411080d01d4190348092a424401c010701402d2030703580c00c500000c0358149110398020564400902050240000599005144529090020604100106002e00e403444800d41c010011002200343c204000e400c070a010704140a4101c2e103981e03841d500188005510711888481a0822040009440b600d4400402e030b41600000e80c1d00d0101d00f910101e0749988505 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 102172023 1250 102170773 102170777
    0xc0d08061807080a050106051201050105090f04050112020411090307030f030c080a0e13050402031207020a120803070801081902060304050c0301060303050a0e27060d0609030807090e06010816 84
    0x561080c40000040c4401d000b1803003036540d0906850007100359812100180c0162007844020700035040d040d5200c04c8a00d066480a11f821f50311007000c0070100d00c40c0c141708484280e02508100001c01c0c13039011205180e41e000d008880502c02c0d40d01d0748960302000d00c40e6a4655825411030142400800c000c001403034030161091402200c202d22030b407079a45440e08540c00d0000054a02d0060003914503003030303610f6070b45140e070f901d8108a141001e9000aa0707500480c1c803d00314496004c00c406095645910381500201207515210060150501e0441074a601c2291110080313603a0500120703000c0c1c80052648686507010902d6020000c0301d808110032038100410445062140032a11141d548007802200021882a100d50303440b4880b49401610ad40e0341305001c01d01840704400450b050241c4103608030910640010190180c2d02d031440032501300c40c181c420280440341007000d18010582d000c05000e11a00e81d5a81d40040b654403003600d041c00c90015105140003503048004160004441026842c50032064 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 102173273 1250 102172023 102172039
    0x30507050712200105091f06080a08091203040806011202062503031a0303190302040b04030b040501050a02040803070b060a0f03060609050c0f040315020d06150f050c0d0806 76
    0x41d5030789011151072a6491000116006206420030618400010200c0361050091005142010089a5640314400d0806200507021f4100910f90b0403544004064110034080d00c100c156541090035059000307540030b81c082d9039801414010100088140ca00b610040e00180c07005034030340b41c2e03a00c000060b05002a0ba000c00204000060108840ba02e410041c19220400726061010700703014046a0f0007040515182510100b421010b940c044129908205640007000c1041c8440c0001c034001e000365003000c814004001000300910860030101485284500b000b8005941e03500807250581c02580b19011503030b44144806030014584c909400d07441800940342801465880d094105940c01d1035009441c2c082c0d855005110129107402110784c044403090075036181c4141c80080c20120702c00d9200c0903042d00c4070280e464510082e1901100c20070800050203100060300c0d0716000824400c1e000151010503070411141c50b44074080c40a80304118210000f801d5002d01c8980309170794082005004652144031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 102174523 1250 102173273 102173287
    0xc03030f020403060911031b1309080c031308070303080c0306030f1014090109030905091f06052503050d0c1403090124080a060b061b030915071203050705 68
    0xc0d034400342c002580070f440041491211401c000c03090b4111400380c94001d81008582039604c2000f01e522202c951001c0d6030f44960902180325071401089000c80081401400141240742a20000090460f01480c0c8072480010f640d2030020316550501031000a020a800c5400030321481164006107601c46c0019003582d070031602078280d01d410000c0b54107407507418030351b1044081c00f07240380303011415403185960000300f0254030b19031000707009038129204852080d00030381d000a00e400e42c10700a41e640201103003008030f09140c849001620540080c083d615030a02082880c08920b00c07004401c42500341c15454551400c15508016409048110346e400140141110280400f8134000000c6101c1c0b2003a1000051000c02c0307592020818504400d455490f542501040c040f1a40205601c02a103038450030000351000c0910105e4114011000d0b0703c82c074203a2910894441c5a0301000500b2086002c4449241c14440e120102c50f840c060698044d010083c4141400a6540280e0240790000004e0030030300d04040c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 102175773 1250 102174523 102174551
    0x6040b0609040e0d0905030303090a02040b0a0905070207180b09270604081207080f15010e10030c0822060207020301020702150d0c050703020a0f0201090b0a03020912030703020703030c0303 83
    0x1d410340c4081c50f541c404000070041c142d2001c1e500014007030480c09035180d414483d440079a00d0000c1413000e486a60341d94641d01c0c1e01e507900034080c002003099180901c140e24137044040d440d486148038005060140050352000c0c50614031401000b0100100120400c0d01c0f000e100152014028160700c40b40d10428081c451034005c100070441c8280c0c030440110307030f40b07401421802d40e4040c400f50481d030601c030b18030040c00380c544a6039a1040d40144003d03001106043c0500048402c0002040c036180c00642c4d040c1c41e50b01c415410f40146101050030b859070340d01515025006200319540000600070149043d46010000b803140d001003407410f000900160402d6410b030009801d840c0d5408600a9107000002c3c01242d120305402484442c011608180d414403016841c007a440c0c0060300b20041007261061280f80440e8020703001c1c0300c0982203200030039032241040a4050001d510628499100309419912948922400004c40e4042036066025105003031643d0340a0355210304005d802c4050549501600b00d6a007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 102177023 1250 102175773 102175781
    0x11b1b0b040306061205060403050c01090206040602010c03062c09210d0e0109030509190e100503070b0307022515170f160f030b04020c06010e010f03050606040b060904 74
    0x400001656901e51942c600501240c2c040e90241c4401404035882c0c02c0814404101f03030340d0207601410020350700d4400044450041c070710b50000070350100004c100030652542c1507001c15201c0e6119102000000e03250fc40b080ca03586441941c01e082c680c4101d4801030104120741e41242c001d00a0002c84d030b121600201907091000301e41c8500540494049591003940000d4010b1040d455681d00080040e0340454a00404030310403400e40390300405600c141e8030011041c3d031215400514204000061078181044400710074001c600c00c2d14440d228403031700454000e0700c1b80101d0303010f960320b030300140088413811740060036022001562000307400b41c50500081e991010111482c80303051320b81d01c01100569408154240000240c0942c0601c04080e007000044044184c84000d50946410641d0480a480380100d000c0c00380600300581260000c16903510504001800a040e1030511b032488103940c1e203441c2c034811002130900c0040c00ca0b40c855804680a8200340c0d11045241d54013410403441c1c04900c1c801301d0701351 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 102178273 1250 102177023 102177029
    0xb0a0902210c0a021212070c050c030a0602090f031b040c1107060305070f1b08030603031608091c050a020411071b06080705090112110c06091c090302011b1b 69
    0x70b000103510035943d03030501c002e15030100c0310081c15003001c164440c0b40c411100000c10050a00a441c0004024001c08001e20141071200804071703000100141380c0f80f006074000480c0c003030143c83c5503c50050030707150109003e80d40d024020b043c84000d4221800b0030000d0203c0a07000c5081c0580702041c40d00251f014132090000e400c02351000b0900741802000189003010740303294401044100c1c80c04649040394000c4150120380c200350050b49075140c0c40c00003420740c40340301090301800710500c03c2803081240b0b54010305180d01040720051003400d20044c801d20100c0d58440014160303040080350000500d011360002c1405071000896a06008960b036508040c0740030001c5c40220740804800400c01160b101d10701c01e41c0f180540c50b015007401c00d4400080d1180105e440350420040e2074110101c1000c0d07040080c0c81d103903031001d4121091414496091a00c4401c010009182040100d0042c4034a5000340019821a0f60607540c5d240103040312000420300c803039174100c11154202c0190600d24403880090211000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 102179523 1250 102178273 102178291
    0xd0215030403080601030c0c02010c230a060e06010f0306050406020409141b1309050603010921030f14071d03030c010c120903020c010c030212070c09050a0b0a090221 73
    0x1903070519040c040c0c00e440c401000d141c1090704202c42151102c0c4d00c04c0142480690a007419080d043d498a440a40400d010b03080364000c4030348950040d05034000040c507016040c091941040500145080307261a1030007406400d5850102c04020400219594410340c0e110b0300440005040a84840030a001d503111050f11840b20008101488035070401c03020050b11b10484081d2941ca0840000c2c03002406040c2c611503e540c0696480010345292030039003290b01c0240e0b110b00c00500b003c0c0c10180102d520343c01c10b014000040d1030640000c6034100188155482906821403038403440d44d484100f19072403480c58514201c080c074191199038444c1c40420180101e40500f03070000c142c507500240c004015810482002c00481d040101000c08030b03030089101c0500200a00e0018031108580c202a49444c2c03183d40f000303000c648002202c00920242c03216040c203807051000180082e0b101c618100094070002541c03071340d01860301202044149140c1c1c0c010402c5503084007a1144100c00400d0282401c00100c034134401d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 102180773 1250 102179523 102179527
    0x5060f0c070f0503060a0504020306070507020a150201050f0f04110d030c0204050f061018150c0507080c09060102031c0b040f0f0617060f01060807140a0906020106060e090604020304020d0215 84
    0x1000d031506110745c0c1c2e0310060940c1c0c10480c40c03a10b0f40010390340c1e8a01800450a102000a048041d9120900035034060130104a00d00805400c11100034020081101c800300c0e659408008164000b0846c602d490140d50007030144050184101e0400842d06280e0700203c05100414070640d005880e540a49445450700b481c80c8a010301e01041400f070540c01e0010010b080015609121924103268a410425114202040301c60016182c9003a603041c0c052080242091040c6440003031003d400003000101d05400b81d880340b001340c039401c00599070390184403040081880302442c850b090707104039880744000300001400801c1c07680f4403005130b8085600201c4002440c5071136000034480021003c1d082205203504600400b0030f445d00c2a07500920340c20600030700c420012848042601180b03e0100c0d6202d0100b54950560f0390019a00040c0c85c0380f0a80c13240e08017650800078001040790048082840d802d1001e001450650f0300d05e81040020750000b002242d1041c2000b01c404007503102e00c81c0700b02c0780c0c0100c45130942d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 102182023 1250 102180773 102180779
    0xa110102060105040623030f0f0d02120405010818010f020a05030f061f030b0301110a02010b0306070810171603051b0301020403080403060504050a17070312020903060105060f0c070f 80
    0x90800e407058101501480c20003a0420908021003506866120061a0340b4131083c031050000f4240802202220050301c500c10055090500100b4119449081c1d502160030b03200500080c042540107620405000c5400c20b40000d00080604400344003421580000140b00080e90500d84105e8022242e80d10001d00f02008100100045603005a00003038122a002c901d000c00301020030b0010f402d0301c9040d0070151200180381698809400041c044a000350300c0c0741d00c440066038024000c10110124a21071320031140031a9a090041d182c4a0080440c4950760038500c2c00c05503000800c4440e40640302c40351044d0385002401803401c4000303102840c810f03005424411070761000c407070802044254003446a441000b04000089820003114102c17a0b01c00c03800b0402e43d8070b500740503080c4600284042c01040c11003410055500c3c52500030211ba41c482c3c0c58482c048854070021340120700543c1907a07034069118000600003441c002c03000e000d04507480090307e0b15240c0e507040d20a040006a9210010800e40c0c03242c14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 102183273 1250 102182023 102182027
    0x7030201090b10140f0d0f03020a020a0e07030506010f09170703020303032712120c07050a080301061d0307290a020304090f0b0a0b0f0f070f03080906070e10110a1101 73
    0x4081c40c04c0e8100e502c41e4840282c038000400c08441110000c2c038003060b6011203810140244000c0722240e07001070031810301c00d5848107034550a41040b1007900029151000050b01980146404c5142e070025a4407003408909000c4d0702e000030640c0462a818900c180d40c40040140c0d4108002c501c07800e21108100c0c0a0300842c402c0c0912a282901c03860050342240e1a100c3c00110301400303a40503100c9003101144152260340704251148504080948540152a158400d00c401d040c0114101e640c5650380c070a0280300351004400215100c034409515420141d010450f42c072502a0200741c91115404032400301c01c500f51000410790250b0308a04c0540c0010034100040c00d654400c4015000140400b8008102544001141c400550041c000b507840040740c4214030080c2142590765608004161035510600e030300706a0440c13820a9002c6002440b42c40005d1904000499880c0c0541600d84a0758800d5004a0810004100c4040410100720400c0601c5580e4442000300d02c02050007540d208008610f03040c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 102184523 1250 102183273 102183299
    0x1020c01050c040e0f0a0608030c0124050d0803060f030a0f0b06060a12050a02040f08280203030a0f0e0a0303050d0e010c0c060b0a030501020f030a0b0405010e07030207030201090b10 80
    0x10b030b00c1e81c04402c0c48104480540c60f01031a6002c110701102e00013070750f1444160f6004010f9600451000c0c40040b80180742c0307107015840034207044040200d0360046044006800e0001016015842d08480350108110010350b101c8061504084010b00044030f003010360002c2131500b841900705440740350311459a00140700408440e00d401c00c9069070001d207841c404100140c50300d04907028618100f85c0da080000c000d400c81d603041d034000d4140035041000c1c1c165640301465940c910488400049160402c40300c3d0841703103407802c9040e40c95018010358205030f46800d058800680c0110218140083c1907600c0310155904401040038612036250326859101014aa50465850710005034440e8545808901030640000018078a80d601c444082038511300000840c08044a982c8000d11a40c00402c04100925210028502c80c90b070b8014104150b0260904120a840c428401e00341c0c01080440400c461600c60b400810046020b4000426140c1003903584244002040301d80302108641017006001203903e40e01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 102185773 1250 102184523 102184531
    0xd050a0311030a090e090705041d12180105070c08010c030c020f0703050613050f0609031b010209090103060e010209150c070602010501080606220510030209061c151d01020c0105 78
    0x2c1d8282056050081d03e1168030b03009400b190900900007650442c1d003000240043c01025100340200442c9100d844098981900080401d015080003018014044400e0b16070400e001b004c00060300c01400700540780d60380a1841503400e0800b000c0c001c9100d003400d00400300302d5012941c000070090352041001341400d88081c042342c1941c006000c00c00c0415000641640c00151050058081300c80e01d1030050b10f01080e01004007014010402080780809001c009400914603c0c0b08007200100200304840c00c0344540c810269000e00402e005001186a42d400400300e045010300051505054400142c0c07021071007145142c201d440003e03d030103509401e0161000408090000f40160350500c01724588a400040c10280500e002c85210314140448040c444680e1100c100708009509050300a0001803581d030105901035065071000c075010303003040925400080c0d0300c54050400c62809a0343c0070540c1c810503842070b108544075951740303241c941c6c4144c1040481900100041e030720b0301291009405e50704018 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 102187023 1250 102185773 102185807
    0x7030503190c02030c040507050d1b020c0d1a0411180415020403050705040f0b10020a06110c0d120f020a050702030601090513080304030314011d0c1e0c0307020d050a03 74
    0x602600300503100040c405c450510300b1034000c511030383c4080381215030340102e003108050981840c1000a00c2c406007990003960031780303030b0342500c0520203890148001c000003008014455008542022104000b0304150f1360030034404d1003030981c050ba801d4001002003a0200c0c1c5015200205400c4c4010000c506d09011002d0341280303800d500f0a0310710b071145c2e0b0b11007019106183c02151a1a10000100002c1c0d04ca0b84030700030004c005414101c010718000395602c4500608070b54092501441001c1079011314180c1d084c00a520000341194010b41c001120f40d111101a241c00991f00e950301002c8000e428006030511506a83d0750b151a04494010149000c006a01c242426460103090150060118103104e00c0030741c0002209903283c039503141c00c80c01000b1090346003900d8030b408000840e481844140285400b250010440900d8a40d140ba62640e4414034041c0c03030390341c401d0f410059006401c24015018030351241094038182038082d00851000302000c8011905a08101c20040c20590018002a188003543c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 102188273 1250 102187023 102187037
    0x70305090d0e0d060b040f05040b01090c17010605090a030605070c032303010b13090501060305090c01030606020d030e010e0f0d1707051204050a1a090f03070b01090506060c0703050319 81
    0x11034041010020304000141000761034294450f17a80c0c580c1c1d04074003520352070350000700001e10300380c24442c160503030a000704a201400c0054000d2403520460010703611040001081c15264030748a4103480e158848442d60381c00074070403540000814520300c2110b118000c6501c41000d080c003a8603000f41001c1d41910303091803640080505454091121040d24150b0b150b001a00b07550b80c44100c6109403070b003659403107000f00c14149000820900da054100d280240c200f80c04680905406100540a0300c400d40126001603200b06031440d981d0b8031070380200d108450700d00d000040551030071818504140c6115600c80c21a03201140b44c2040c2d9902c10240a826102154540d500c1d04118000402c148290500c807100c48003030740080340502a0900101c1d6106a1107041f110110384420004140e510044524030354034014800c24141c0500044111010503a0194004641d6801c1c5580e40c0d0007440b000e01042d8001c1d10900850103103000c1040740b0800b40d806070006549400d02060000400200402c10100700514 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 102189523 1250 102188273 102188297
    0x60f0602011b08040f0c0f031104020313021e0301050c030609010f1203050d020c06070309140a0b13050a1a010807051e0103051504090c030507050105070308012705070305090d 77
    0x112104402d41000580b40c0354660b610346040500c2c600c43c1007600940071150080b40003a21008940b01d01048901c80d80030074120700c1c003450412040380011192030942e00b0620f581e582c0103141031280c2401c882500354245000380c1d0200003082c00c687d011151074a0840c400010312142e443c0a0082c0e40c014032201e4400c006e49410004840c0d01c40765061401414803c3c049020111050780c0e4064941485803402150541d1810060040241003c1c12080d00c170164484181812144041000d605190308000320480e980c4551680e5104040b1350308096074640a0240d0100c00500d22020f240440d032052480300d80b455051102c03071800c3c00915848a40305026110955654020345034501071110001d01300042e195407250005001e810710180d005034064a03043c4403004101e6642d40000c04e0302d014604035414180c039003006482e50700c2803d0018001c6016100108201058000320403425a1b40c14203144541210103804025a002a242580825150030400030407010411881121411510301010306c011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 102190773 1250 102189523 102189551
    0xf0510030f08070b070503060111072d080a08180102010b0117100f0902070323070210020a02090c0403050d090302062203021302090a0603020403080f1615060f060201 73
    0x8500c80141038001101d1860284291541a10700aa4001c48020103602d04140010160f0740100d0b403040c081021004c54000c0d0541c0000c081d13064860348644d0803032000c132029264808642a24505500d40c10b0310360040303400c1c00c081c4003503081544120985900c0c0c030800c1080c820141601e10b101411a850f2052000c07040e03900448260b81c402140c10040b1050726075040b0008961010741002c01c060b0540310300000c8001060b4001c1c0491400b075078032000501d80b0031080302c13a0085111401400e081080c0000c80242c034000c80950b00c41c42d5a401214060502c95000c2780300080201d86020202c040810200b0601006000708541d5619910308407100e00c2c2180e0000765680210501d01110543c1d0b00510034070091241c00d0000919001010101d03070700c82400c00c00d400b940c00701d00b010707004101c821400503045019000351010380303500501960408481748042d050540100315031090581680017500c0c0840c0d10403040e03054140c03003280c004c2000d50034991380c12003500d26980300c10116071509004c0898a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 102192023 1250 102190773 102190801
    0x6170d080f10030308040201020a0b010f150509030604080f13030605160e01020a030503070327110904051b01030f020c160b09090a18080c0606040c1e230403060905010f05 75
    0x1358182000380a41c1c603036000403840c2a20b8440001c0601891100114080042c0c41d00780048801541c03d00e281103d010305c080ba100c1c05000d10b416095030120022400007200c02020380351810700c900c0014104051140445130200c0d00780d200341e903c240c0c1c03034050107c1e02c4083c5c245c101d100c031540d0400303072104440503000075a204400d03200501045404404030311801d20a42013080f4503000450315107404025160782c0b1200b82c544903412518032408811041c0941000d984007403182da04400030700703c00882421408190340c01c0c41720460416940f611080410f05561000d0011991840f00501210480b907072056200c10498208102c40e131820700a20415648404050b50f00c00d00500010030300c4542c114000c107004080c901d00910880e40030911075000b00303002854130310401c2d0495090109602c4640103860074044054400d01c419940fa2400024902501c40e0111414840b0700000300004124100d56007904181c0044603020344030100c55007844802d0180c1c000383c11040208000c541400d0391a43d55103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 102193273 1250 102192023 102192029
    0x325080103021804050c060408150106090f090504030e0a06020109020306010803030c09060903031905120f010302012705130c030506180711010209100903020910060e010e030106170d080f10 83
    0x8003d5100008081142c01d00180301c400002030101f07501c681d160b49080e81c840c450a8003c0031141b007500c00001d0701c944160b620204803190400b1960301030742440d1490024200040c415418440c850641004940f2000303801d000904260340002142d1b10580304041c00d01c0010fa11404543d0f000b4020b011071a0080302c12900f102004540c011341d00c10814011906502403440101450a00b1841031403045400c40014203420b95290b401c0c0c4000c3c1c1e01c458000c0c4c0d0703d8030280806400180081c07020282c11601800a00c3c0c1e4800d001d92000703080350340c0d500107007401013840e03005c500041c2c480d262000b4803074143c00707055048101110981001000c01c40c04d010041c0f00203149004000110418502d044402c0d0f0488600560140c0619501203000e1800340152020307220890042001d1000506c45803640c0750244c2c103503505555281c40c522545c030700440300040c008004075415541c40c00c0010311441c003800d1318045c8030840d0010740a8442c90702d5025040c07441c014000c1215103080701c1000300350800e00c0055019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 102194523 1250 102193273 102193309
    0x3070b0a08090f19052802130e19021f090f0609142419080c07030e040507022b030e0703080f0714060a1a0102030403050c0f0402070503032508010302 66
    0x40c007041ca0805500e014802018803801c110208030306c5951641100614403c28002d59003002000c04140b84078046030300e621004030a40d0041c99400007a5000c100c00103440074001001c81801440380340094001c840d01c0665080820102081000b6074103d90342403c0c01441c4a003400720051f8a8807174036013250341402c0c1900d8450102041c49940d0898036038a006011150501c03883d45917480c0801c065400d440140c0c001001c1008400046d544807002c1c3d045460782507040ea1110743c05810a02070001a1001501090a502030a1006000c4281280704e0748403100c0d840e0b080824030b4603003200141c00c440c03160b0301a43d065000800140007160aa4088684400a4615040d81d07000e00d81414048180e0f205d00700000741c000e00050110111081c1c000301c5402d00e6600c128000f0710300d01401640d8912482c8002045600601c804091629000d40d540d030001602034005490620181d4a00342036902c00c944042c201c860032039800408198900d000000040207062803810b65046400190f1412610041020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 102195773 1250 102194523 102194563
    0xa0e07120b0604090606080d0504090f052428051c02060403081c060803070516080705061608130e070c200a09050c09091e0711030903070b0a08090f 65
    0x1304000c015803120004003290b0080d1601d43c804000700601a9105115004030641800f60b51500c0298a2180c07074000c078072301780712031040b44488070182420051441810390305c58807090480001c1d02c0001c0900e400c0c0212210f0080809007420100120411041100c131207101e100604800140c480200701c6042d41d400640702c64641d807040728800d800d540fa0140802a582c01d10000054031794000000d820346510481c01d982e203214051280e02143d22261148815682c0401340810075400c0c42c00c0140048841640452611440b0780c0b102082540143c44070b24905c0038211702040702040d4140e00a400030309503e4072400f100b205403580c0486801e8403000410384e141d240034149080e03070b50104090081010000600c07051600c90034140d002c2d04032040301800364040c507000070300c040a41c41750003005104c544011005503c0e0ba070000c0307484104403480d01c1d001748020814410169402c010030b10043c428680fa0395138400d20303080010f00040000e410344945a1008842c420f83c0394003c80e01c0042096002d040c08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 102197023 1250 102195773 102195791
    0x30a0b13050d0903030f14160303090b010b090901140d0605090a0218090f0f030403080702010909140a0f0207030c080a140c010b01020c0d03020d0c02060705060a0e07120b0604 77
    0x500804481036006003284240400c0b040140d42110307000d01100c2c02501c401040c100101010b072424030100c80c10f01803808003044842c55600401c4001102e4502a280c005600ca01e1039494426200080c0c012910460000c0b13a002c513203181c0840c9850140c98081c2034060040c4a807800b26030007103040c9000924140c1c032900003a40031541003025143c02030300103080780708103035425098041540054441c1300041c0245c0a0444680300d000444000c032240f400015490a842e607260101c0640000c84124100090f907100013600d0303c5140560319007000c188851038405c3c00c200c50305c4000c03600001640d1400d05d0060044002194011080d0700c1d45a401280c1c1542c0c8404c0d1240850740c03900400c00210342c0000200c0d406142260540c041d15030782d0307000e07001c1300c254070058000c0008100750410000d0050340015406101544203c0c1003030501440a01038500f80390f6542d48860030006c040b0be081a0349035551620000c500740401140c0010034040050b0001d5025a445110f0f05200c010052401030703445400070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 102198273 1250 102197023 102197041
    0x901060f05030a02070809031f1a01050f03060409021203090109060c020306160e040609050402030c0301141b09090403020303040201120c02030a051308060c0d15150f020c030610090e0c030a0b 84
    0x112061f540080c143c0f13010068502c07204c04040039848588044514048007081c0b090541c07542110102d01c16100c16052040c4241083d205a000400c0310790826120100b810050316141109150104000c02460311461314200040240070982c0c400c41c01c011181c021900580c4010070b005030495503008400070316071b1540ca400e85904211203011500540781850010312411594043c5000d18070031800d81d502100381d00304040c20303107642e10444d014139070208000c1010b11410703220821100c40000111405c240103c0b00041a00d1021101034002d60400000c0004541c0d0140021140d01e0038841d04000195007050025540d02980c4c6081d001e214001400300040e1340020304203001018442c044036824601400c1c21000b0b50040c5840f01041800e1040c110481c510119441d4160f0382c010078400500c503034020b4201c0c0e101102c0c003040300075400380075080041a1024804c4511400e50780100b01c1c072407403922440000301c5051410002580d001707407080b105c8076580442d084503c107800c0603030364005484028032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 102199523 1250 102198273 102198277
    0x5090f040905012a0210091109100909081b070b030c0702010e030703030509090703050103030c0201080a15140109050414040303150801020d0504020913020904021002010608030f090901060f05030a020708 89
    0x40224100044444018108901c0060b0b004c00003960f00f40c6901c118010703c150113507410301800504552881082c0821ba003000c500195110b42480e0061040701c0e0360701e0194044a807181c0c1c0a072923440000920b00b0205441850303541d0442d250310300500301e040c83d1032401880744c00050f210b1400c02000044490a584c42090300a0714200020700b41c4010301e5903443c020f006903020800c528020150f140000d0310080c000d1090504032505074403094110540e96004444481c4014084080140e650410385101010301000c04040c3c0740201d19124a10013810001d45050044c0c1c0c07006201d6403e1030800c25101c034009803001e802691500303003c94080700c01d03007a86e030b145641030300b00c4805984007107210308080007540c1102d03000e61f00a1300e0404642e201d03100305201c00b0300401401781d000803d420101d00141451004140d00780214800082d007152a025900d041d0351002c2211b4182c844089250a910300c0e125102d540142044c0c01d0800042210b828040e04a02004101c14012640880c0d040144808441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 102200773 1250 102199523 102199541
    0x50c1c0c021f090614070f0204091401060608180714010306080610030c090b010203121f06080405010c0203030609070509010309021005120c0306030c09040204060515071205090f04090501 82
    0x24030010a115421070718001da010302c02c204005100400d001800c1401281c001240c41111403405d40751920036101c004d070181c0340c548201d07006941e40290707a0200d032000d8440016a065000041481d6152820007080c3c102c000e80500c002c0c0005c143d400760031400c0000c01c40200d60141050890554410f00143e00901581e4040e682602510081100304001101c1c102d041d68400d5515201c09500ca242c910300300d941040400d0f0241c3e004008a0b010410441c580c1035002032020107071070380000d190f81410707621000b41d8030641c0072840420070311041000c01e000c3c02a64103003520040d0305500c2d0040010b8000c090160140043c00000254400c15901c030742c00044919801409203903052104078001029130340000c24000c50f2a080c0004525085140030441c0c1c010070340140200718001c101402c0000c15100600100c0c0d220340c0e10f0000003240c1e107402c6a00e00c840c0500902c0c840d00c41d0f01c41d0424ad4903a01c00c0308080d00c10850104001c14a644d00c04449031402d04058400081d240d501c0d1402a0050031114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 102202023 1250 102200773 102200779
    0xc090301050f0910020a051225030209010212030601080720010c08090f010b031023091c03050106080106030c05160c1404090b1b0f0f040e0106050c1c0c02 68
    0x2c001010601d0215280242d20850489100001c4001c0003001c0f8010001e280001a0040107411040142514010b0700f001c828000355088000c550402000006540f1844c000300f50082414045581c041c804420304c0031489904070325519000300005c102a000801b01c0051202407071035401d101414820304025810313200300070024480306072405000700b041114001002d11034401008800401070094080c0c002e0054001c040514403445442c1c090580d50b01d4040110070500e0854004143c812503841c040c000b4031000e07007400301d404280024203041d24a090390905091070010008079070300000c060b04603412450700041c0c0c10f2140b40121114820f2002c20701c014816030440b40144200f2002240071034162008502002c1d00c020240000d880d150307070001c0c10400d4001c00140c0c5060041d04820003803800f01c4626460903c1424051000d0740110510f090865401305d03007070100702c8a42c0c40043c090007550402c6411b10400041e402c1da21000c0911858011044410008400d070045030060076040d402 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 102203273 1250 102202023 102202031
    0x41101050c190b10081b13150e061507030c031202040915050307081203010306020a020a0c18050f04020904020d060b100203180d0f06021c020304060506031b010210050c090301 77
    0x16040c88120143c0c1600c079904035510b0030744c0004161000080804c2038465003a48201540103c0c0100301d05040342d040040205900c1b03c140512481c0a204100d0127011110006001030400805012003401c1450f12205c40580400c580c4021a0700800f882106a070f051074a51207217a00e4449003000b80c025544407000c0b16003030101c101c1c000708280e50402e0a0711410307401c071a61103a580d512181d071145840043c1c0c8001e40300700010f0000c03618513001400003a10500442c0c03000c1c269545c90107000c000e1030f40694484081000c000241002c18001c0940011000c02c03064018101a0000b590318940544024413503105003016104108680c0c00c914074244000303000c00040c2481c0040a5213a60000c103440c610004282c00d5000c043c078002c0151180c00303401001650307940304c0781d5480d00c0c000d5006407480651103641c141200001c4500c4d00056102d00d100b0000070820381017030018580740190454204a2412914030368844990f4000380402807041d283c540401d140d111182104114400d4021040d095428 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 102204523 1250 102203273 102203323
    0x1b09090a02071101080709060e0301060312020f01060b0403020a0e061201051302040e010504050303010b0307050c0111071101080f0c09120d0305010f080c0105030103030806010219030908070e041101050c 89
    0x20a902404442d4080c500ea10014a02d920044440c250f040710450b0104404010a0003224415070004100e12405000029002e8890329440c1d400c61140c083c240051340007511484412900303003e55401415480560f43c18242103500041207901a4020740d26071641d840d00260311176884106244c104140000208a58207200801915402c071944040e8040c50811040c0b80320410b052140910031030300030000e141141d00b40038242f89143c0c4060300e0702c42007010901205807075013820710030324120040c403100640d44c030442072400c058003407182140f49043c04800c03400c104942c404191a42d50103840b800c40c55590b04104130003c1d10ba0001500301590394401c1902c001c811a030150b000e40d05848d68143e00645c0360780d5481405640310030203828140060303070a100400020b4021071050360080c005006580011030000525071704c014544406400140c4144820840d40d0400d006402c00f608110604031202e144c940c9440031001c0e255400c0c41c4c10800005205404c1000a02134580d4254219620814002e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 102205773 1250 102204523 102204541
    0x6030507091a03060d0203030712050909070806100e0d05030d0b12030a0e011d1206040308070207120f0618110307090b10030507020705060c061017061b0909 69
    0x48211030840201c0c00c81080881c41800401580105400c040d003203d24660300e4000340444c00038140800ca030580f01c01d1004d03100040001904107640a250b59840307449403a05001c00c4030301100602200f0511800c001031080b240c071034071200303000d006040c20001c4003416030102145188841042c050040d020114852814000580000980903411110b00c0000314001401e40d4480c403c0403070039404641c0620745400e031035014541402c03404100c81a40c0c0400100d4001141944805050130f008135049541003204064007d5591904140c40c1d100400d102828082020600f0203000005404a80c8004140c000c1012a4000c50301294840a0b4019401060300d0603000e245200040c1d1072081c0105032000c40d602480b842801c00e40c001c002c05407040350701c101e0b0055008010103032500e8118060000041040e8803114024013900c80c02100819545c58051a48007050625270407a5441e28208450340d6400c0200048540e04168042d24004030301044890303c9029100d0100c0741500004681c04002c00d901d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 102207023 1250 102205773 102205781
    0x90402120f030a030618050702150c0d020313060e06130f050f070609230a0510030f020f0904060b0705071505160b04030f08062b0c0305060106020706020f0606060d090605010603 78
    0x2003102c1b001d5200c0301e0b40c000e4030a00340d50303086400c4401a40090040d204c49141d40d056141c00c015045031141c5007009124401c4103990003207500208001801c07407800304004051162811400c280b8025106a090010030f0f01c2212612a0b0080c00c4540c6080000303082c050203000b00c40016210908442540b541c6090151100202c2e02c500054846035465018807550252500d440382c031802403c0c041124180000c0188034021000800304040e40c3d4441184103201e40c1c4010507151125040481d00c4101d441d0400090ba60031340c02180c90003200f804602e001035000a003003c1038940c4416102c001d880c55410840716400b44920030401d07855140485001c0c00692115180514042d0366a08040c00c401c00c421f0701c000384240c8503203411010b64010303122314903219101c7e0188a00d45505103002c1040341e48401c102e6400d550016185a0800300041040e035804201d070400800a5002400e02019404601c07502c411005042c68010800020550f8654000d0b600410043e0780c000320401c12540c46020040040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 102208273 1250 102207023 102207029
    0x30203060702010516030230011509080a06200a080a060b130302040b04110d05090c091005010c110d0302010c09050418080a090e041505070806090402120f030a0306 72
    0x2038003440010606091042c0607451003040312210b1540100e074680001c078000c4d407000c0116141300d21501e49084a4589a078503000c014840d40184401550404080911041c11805074200340100c4120401440002081c0c810401d03400003400540041595641c3e50350340f202014100001000088200c420f5800407a80f43c01115805010800183c0f0703000c1701b2403940b041d0070420882d41c000400c10001854503030485404950040c2000c2411120400b1490154200c1c0ba080e200450310341c1c2c1040080d880801410401e00c2088802d040a0300f001d51404500c81c140d405818108240c5a0704103081c00512102c61001a038081c00c003050001c40d40c10005d0007000b00b240d5890001304403810014040c5443e0107000c02ca120303980040e0b000480c16030b88201080c3d00007035440c0300b8000f98400c000f0b0750050340c0c4041e6108600a08640211701c4150015a003141d10080503241480015002e001d000e440d2440c841cae42c80341e419590798000424046100e484c01c040088048403910001544203070f00780d41a0407002c11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 102209523 1250 102208273 102208279
    0x10219050309100c08040b0c0f0a020304240801090b1f0201050402091803040b0309160e10060302071109090c0901080d0806030d0503160c0f060515150a0c080d0e070302 74
    0x450f1807401c68142551600c010080000301e200021501042c000c1d104160490880c0d49490f2034240c0060309018160000c100c08000b5800100b0308000018501c00800e10504805d141041c000c4405030000c0e05100040c01544081f65548044c07030001e444031600303000e050301e4205000241c2122510003d019000444080380500d05031000729503034089035080000e554150201035802c0c107003480c15151060704001e05504851142c0c4a1184014490344800c6010b050007049511051074140401c190707181c0c2c075502c00e1080510400103000480c541104101250303c2c11101003846854101185280216041ca000c5d480b8078040000141010001034562141d081a01c1d4156242e461000b05034440c00e45000b1480030950802c00219001e404c01224503409140b405c0c150f601035803c1d202c029944c02001d40c11101c003540c80080c018402071320440010200011180c90303007130702075401051031940036802c1d002040c001400c80103420000e011060300c001c10071508040081c0308402c03041595034000c0d8402640 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 102210773 1250 102209523 102209533
    0xa170a09060b0f0312070203190f17130605070201230406030c0503040515130501050109020a0809030a0f05090604052707020a05062805070e010e03010b0d0b0405010219050309 77
    0x314606050000c001d4030500140030b03015074005040b50030f43c00d40c40b80f102248c0c1030191002e400104640100404201401480c903404031111902d403e03c0c83d010414010202c0b24014011001d1004208401005417105440c0158980382d1500c0103881c407200500d007448241240b4981031081c03c03115005442241d000b55424804c40d05060340507a42448152000341964002d883d240b115000200e4080b900201c41d603484545d4080252030b03050031204282c00c00000d15400007104403100c1d40c0702c04c407290032441450140d0710300140501302510b01c5031024414014420f0115000506076580c1003510000c01c2c2c09070222040252000680080848804610f4442c007822404a5030442c80010414a0b5a502030010001921101c410701c0b070129003c500e28000304000001c1c0300c400e0807203005040c0907289540308c8800d809880c01c005400f03101d045408900980c90301d0300c4005259a920321000e00c00e50003080208640e146c07400e00501900c919415070906c0088081e00301e451503072090003144a0210481607034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 102212023 1250 102210773 102210791
    0x3010218130605011704050c060304030804030314010501120f020d0603050309130212070c050a080d051006030e070501030e030d090b070912080d0e070f06020f07080316080a170a0906 80
    0x84121840b50007401d0000d4013901c640212981540001900303c2d0045080728511469100020744a5000321801c81c0080d00035018401055090f00800c4580740035100032100d590b0502000130f00c00103112031024400c2c0c0e1205042d1480400c95412aa0074050b483d2042c80720545900f400b66a0380d2014040d18000c2408468208580c0154420381e022481ca210000c2d100d43c03030380c410842e4034840c0c40400f603542e40140940900010544401411841c2c01c6210100d21840d14a4002070b80582540c8003106050034448510f090040120f14003040c2c400900300022041c1356211480e00d90301030b0820080005113030640c002c0c140524841010b05c10704c00c0380e448030303000f135191448400d050cc2d80d0300009001480c140071a0905072456000f04090b031584100701c445003a51030010803c0d00100f984414003680082580c005a41c40511250001e0007a0000461030b295030501d400710b000301d40d241c000c0c0c03900c08086030040c01c84c0d201d0307001592905403d1807904c2030342c104803500c8001002910301c1210060b280410003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 102213273 1250 102212023 102212059
    0x120906080f040c0612021213060b030c0609040c1106010e090f01090b0103060c050c01060f05100309050c01110307060204060e1c030f0503180609030d0c09032402040503010218 77
    0x10b128941c00001121030a140c03420a6903a0b1011031811806a1380a01c20b54014114500650788181c17000e05031540c145450f4103148080355061034081d4002d801c440c00201c1c0c180c03034000403607620003410b81d00040c003c0440e41d801c0b605c0424504880303080d4040d04000044034001e0007400b50044c5c03501800ea91601800010b09030823580c8620380140500030640c010000b10708185c5c44200001c289060092130500d480d03802508685144d00035844481d4002d0040c0101e0815820720143e410050030100300a07c0e00b034440369903941580c040c0d14104003a107044405c5412040c0f050320354984d4480350a5454a0301e07002d0140c440580c00f1011400b801880f44209111001d940c0c0031010107405845400390a41d01c02c80480300740c5c1c0010001007140070100c420303610052041002300d12030402000a552545942020319040d00e084007941020400c14250500102d5480f01000d862801405080340c83c00e543c4c8814400a40215801140d05501c00b003000c1100900710408a504440c0884000205041c83c101d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 102214523 1250 102213273 102213301
    0xd08031608091903030f06180c0201061d06090601140301090506090c030408090d14100504060515011e0e09040f0201120614040b060903031b07060212070f0f12090608 73
    0xc5040120030700f00101020038041d40c8541d036003080c40b08011800c15150b0b403031101e002c1849a03110307031503a50f03604100e640e5640c288255800742c03400350042d0845000c000110581003c0c050300341c0f44140c040c5008201e80fa13010300b024031030300303841c080d60f09403a5a564040c00009000484045000b02500c1c070003e258045510f08a901c0380f50700030b10203030400c1c1d5944140b10409800b00300449440403500d03034951025074104520f0070908408071002ca42c5103040d241c40000c1d92809400250101c070380c86440c04042e030b00300344440907860250780340300c100300c42d02d010889240801203000c275004a00c11080c04180094994000d0450303000b030b205d4030b4100c0940d8605130b00321003180c400c1c00c0d00300c040d042210f034013458107401544e00c2641c0140308900380803101c0006429984805000c3c01c110031020950340c1b9516090110400800d420b002401306405114103102c4a486030f59401850078903841032007070030091310300700407280950072150104200e4140d040140017403915015910100f000400007481030464601 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 102215773 1250 102214523 102214543
    0x160f1511030f131103010e100b100e01051e07030f0e0108070e0d030201020c0601080c011710051c060608010c0210051012030219120e030102070c140d0803160809 71
    0x18040040e039840301400c003c1825545401c541d0360342d50024140c199078090140c00c2e42c3e203441d00c0280c1000c4140c89505000c8410084a0300c0c003800741a4480c0e01980e410a1104060400a0070300554400705000510910703a00b455010250000c00b1407410107050b0b04c200b078061400f0103a29640c101e20424030040d110004111400e0000414a0a850b075090800c0904451010b10a00016041c00d161096160411000b40c200780c0c0d1940c00701d1505900f42d80e210340606d02d441c80c14501d03444981000103400e008000075019450203114041031413000003810310b1011103202c1d007095080040c5901c800082d030181c450b440005c8018420340a001c1f451400c2441200d0062180d03014540d092407400e401c0090080b2401c07403e90540c0560000c038050911603541c6400218400c8600d482e01e01d2442902a0000560b261780c18001ea205000d031100280266106200384c03001c488440c00d07031260050000e50311070365810300104582d4011013400114100503952420100c8542c55090712960f0b292541655545105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 102217023 1250 102215773 102215791
    0xc15060406170d2006010e071b0c060507020d080a08040b090d021b01032903060a0507050a0e06090a1403010b0103020c0a06151d0a0c08090a08160f151103 68
    0xa4900301e001800340804c4904070f020388a210250983d504162030400409920415030801405c0030069030030b030f1100c3c442e0002c1814803540c100c440400d80f0350307540c11001030103007006000e400240e9400390340c0c80d400e5191b841503201c035005d42d450000d50307801800c113041601c045804080c01808907a1038030012841c0d20083c0042d60040400aa190508040000303544d2a03c90515680d184000303c4d5424540326840b400c40603c1002829108003018140343c000300401c840041d40c80c100601603040c2c5d00c8001c40ba038040445c600514441080c1001541511410000c2035001c07500e402c002036210440c000700101284100c008204501c10400158140c0c4600144034105030001d07410f03440010066072102c82d2810b00a002c190806032103503091000c0b42a2031100c01d0309803000c60204590094039000d8900f651845150200031410403001c0166101c1d107504001b0200349012525070104a0024840907003a500001c40d043c10032090f040021402d06400b400b10282400c008107807042000e06821203000c0e210103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 102218273 1250 102217023 102217033
    0x501050f03030f03060402070206040308041a03160804170408070602010b040219080406020c01060b07050c04090201090603020c0f03130305060f070905060c010b130606091a04090c02030c1506040617 87
    0x102044100c0d91344001d24541d4025400d0180c440940c03100300c0900065481040345664560074400d05200e130058443c0c1624104c0010003c1140038817140614180d0741125007414105611a454001d000c901092f205224850000c50002100e000020304a42200d0b01500200207a1071a1800d100c20781c0300b43c1460160300c00c106038904400300e104800d42d992103801034000505110708030030030354259400c41e0300c1009500360208410f81400300600490000380c40c08c6404110352130301c0354000b820803a110311070030301030550100c2d408091b01c80501c441c8040326000000d99617110460b0a040c20343d51171318082591035101c4d0034005001c80b61071101a500a2041d030321809100d41c42c0c0000c2180a60100300090a0703035403140722086003a182c5058070f151556118a010600c01c0c24100b00070703c924090f80c0070015111000c45031180004e2842c040340c051b143c248034041070001d41c4c20820b9240d4840c0381180100d80c41134508502d15607560190b100d0107680112024407150b540c0302c4200e0043e05007055001072a400c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 102219523 1250 102218273 102218287
    0x911030106051b190b0c0705060402090604090b010305032107140a050c0d11190215180a0306060609060e031b240301030b01120c090c021c0f030501050f0303 69
    0x5030b4007400d0312107461108034000245003c0118100550341c0740e04401c01003241d900341e041000001c425070340f0075020f07540309041420796203c1540c0c900e80640068065094000400c1051300c46070814641250014000c90880d6524a040341d621381c07007421080074070109421000c10740341e541080f03180682241da9606188100c45880c800c55035002d251500c0c1407110800518000d00300a01904c401120f07152140080c121000c000a030034060900980049091601c1c6120b0060b50380122144082581c525442d8403011020300005244648515042d440000450300004001043c2c20a006031a81503591300d03c1a5138a040a40340c14400c2440c696064009140b040d0006082c040b40e2402e00c4001081121400c1480516901d000c2c00c2c42081c45101c0e600100500900041c4001c05004028007029141c1d031448685982c0540d40c0d01e13001e180e040d103441e81004280c2c28400c1082c0c42100781441440340021100d204003030205000d50003c000480d050074000910752a00e2074002d22000782c050055454184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 102220773 1250 102219523 102219527
    0x8250f051e04170c150c160909050f07061209050a0204060b03040303180c0e04170d02120c070c0b0c1218100f0206011806031a1e01030203030403080901050d14060a0911030106 77
    0x30034880046ca00c90b4058600c0304090907140a401050b1000000544100c241081c2341130a501e082050351543c028607040103400ea102ea40c0f18407001e82041c0002e03400308107280484c10940280b1010794014105503011880305a264010b6000b81c0c800d880401c0384107044035001c0103072004002e014241108001040210540c6260026070103481b401011031032800f0b0707400c000155089400d048200607130220343d002ea483c40d410200e5070041c0000000724103000c070a0760750b00400b041038015000082004203103421480d00401100041003007100c0d00c00d407901c0030b101000c44000040340e01e02d4842c4440000c0703030b51210301426415800c941c1c2d0b50702031305040c0c4c04c04030f1203603c04005120a0707c1c0300c0e40c1c03508004041030b00858a1a0000d507042c4c24942e0301e00300010301c0104c3d80b183d404103c1726400314400410060ba00042140c0c1100d900c00c02540c0c580e4039410050703407140100c4503800545410030104141d418141d56400e031055004413074036545217071682d10f8402156000c0361080804d81013040103000d01c0b8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 102222023 1250 102220773 102220777
    0x501020705010c11030a121101110d0e0f07180c051204030f0207170106031103030a05040e0c1c06080706020309010c020d020f06040608060108250f051e04170c15 71
    0x1d00521462031690f4004c03011902e42496041d06039528607090410304c80c601da103d0003c100d00034204000740312034082041c00a40d1803040a01e00c10925684000100d00f9080501c5041403066a0b4400d407140c05903113203c840344100d40b540081c4182482c1c82a00c04408c3c2c000d01c281c401d00080c16028003901e07511641d040d034800140002c031506521a10000044155a0388681c036400c2c28854000315000b0715500e8501c0c45981c60340507081c4a13410510460300349651200503101250391002d90102a0386070a04449258070915446d084c40041d0350f48052031440107504004200d035075810840d4001d940d40c02080340c40703003c0c0302d0355940029500314240006d03160882407040359600003408450040f503048000b44490340301c0e900c60701c04164020100091923800036003695004400c40d0b0300c000403c4030345585003a081304165100041c050203071088a81940b20b203041e03c482c40c44001c05020001c901155000301c80e0814406c00d20007070900c032880542d803030011560344e80d80f82d0090308070343c0c4d9214080002c200ea5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 102223273 1250 102222023 102222047
    0x4050309130615050c240c0a18081b0603240f0603040308041403120f1008010608070302090c09060f0703030b090a0b01080f10050d0c05040c091e050102070501 70
    0xc035194040803400d0861124600007510f4161142070340c0300c511038100c1d403c15411030192818202c2203003001c20310140e621035a5902a250224407a0354a03003405c5d041c0c4100d412029040f0188055500210b0001d000040a1a41c25000c201a1902c08a03880800c03005120456200030400c0103040c02480844240101c600d690750300401c162245a580f001017803071500300f154150b0025070030780140410301c05200c01c40ba060020b250059480c1228010700c0e900750f02e502601c40c00c1c280a00d0800a4041c0c10341400d0440507041c0784000340882175903054859640c80c1e8502040c2d100d0102c1c00d02040040000400302c612101c000b400190501403509130030b14080d0050001070b414141ca13805080380660720310200c03d00c20250210005054802c1000042088000906450b00f1340413000a00c90310850756039000044a4040769001e200724502e14160000490940c4001d40182c00d00d117424030001d411094840030703643d040c0b500f246900f401100a19009115104050140e00100000e0009511509002e841 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 102224523 1250 102223273 102223309
    0x1203130b221a0f0d02030f1008070303080c0a031e02030109060e19150e0108060103060b030102070c0e09031608190504060509010509040608060901050403181a0703030e120301031101050304050309 86
    0x51031184d941c1ca409030b80c000c46a44003c0e000071410080d42a80080154010740000c200402e0110b0a569000c0d00c1d081000d0401c03034030f0043c0890340d181200e00c01c1d04040034a0f42c0d0014078420107055402d918010b500203006440f001030030600040741190224441502c142140603400c010104a0700f41c060003000e951902103449044014003084030581c040c1024000d081d514014216136245041034000ca40400203218405d1f40104904070108485000201c00da40041e03ca4400f280c070340c018801e02e0741c812028141c400c000b1050106042c014450080c01c0d2503c0d810104481c041e00010049480748079600444d000700b40c0501044042d03510a60242c10360300b07006400018221f407248441850900100d61400c0140c0d1245c0070802010f52065403481c18241409003d01c4030341c00c0402000f02d00c48482d080c00c00c0340c0800315070002494401d0300b001103c100040203030b80c2a4017501c0d400c5d0b4080c0d4000d000540310700c1d00020001991b0b500c42c40440c1e10079500131010714101140c807030401c61102c07104000301c08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 102225773 1250 102224523 102224527
    0x1030b06041208042103090e010b09090604180c030b15100e0f1216090204082a0d030906170c09010f030b100c03080a1a1203130b221a0f 60
    0x14205117045c04503854003030641d2500302030610918005144055030740164003400007501c010800007110000761080144100d98074000e82d5980804a0300401c81e01c105010b50601603a010428001c414000c80280ca005c1c421000f550f603104145c200e5843da88031601c54211a050040220282c480c4071000c400c1900100040313a0451020b0000320010300035003500c4155005010210f54001903c44214002c4c040c81000b0b40c1003901e8110095202d42c1c030011031480e00c0305078901210a04100040d4450207100041c00040c03900c07032509000306000c1280c000c0d440840c0440e0f100c0d2549410205190f885400441081881c2940600c011070b48008990441000d050b19844400e001c1c1d500e8030064901c040003986c0d4000c04070002d060003860311b1400b9003070451003442c0c032045580c0440b40c00801c0d4900d51041ea5050704601103801010702d113201d035511a010303040c0342001c01b06954a03020004d0045003140c0304000d240d0290700c8900108513440c3c3c8075882d1b42054079a001c2e85010458405000800a0190064 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 102227023 1250 102225773 102225779
    0x6111e0a080c1903050409050f06011b05010906050c12070507020a030f14010603110312070507050409031103030a1b0e0916180e16050a02060a02090406080a1104050601030b0604120804 81
    0x7618103c070001203000c100f0108091000c4040e83c0310f0302da0b001070b01e1f10078800107003040d20001e4507a4070015134002c1d442a5032424a1309201007504003800c0366521103010810780c61f050807107006a410038034800c2802c818080c00b240d6814450400d4a40c1943c00901d80240103145503500412485146400c40342da030326568035880b84100a105910007103005a50b00c903026400c0c4070400d418100340c00402c1e00315080030310000c0080341b03001514600340c40080e600041c0f404018102034610804041081d0340a00c0000304004110209400c084e2040400d0200404429107800e401e545000c2d12664807034210b5020400500c3c400c1d04003c0300c25850340c442c01d05110802c7c5207010003001c00201e801c0b5001c1c42038240c0a0000220484002d070340c04845502d440750a000e6403440c02501d0394005860345039401e07004035003ca5584d41c0c990010000b030540004640e400314452a01c01c1c0c6c44160041c10314407a500d0000011411350282c0500b500f9103400070a2185041d08044c07d4401041c403d20742070f980c00d0002d000c04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 102228273 1250 102227023 102227053
    0x90a0b09040b0402030705121209010309050a060b010e0604030807060504060b0a0806010f0501090602060a0c021c12150501050906180405040f0c09020405060f2206111e0a080c 77
    0x21030141d80a00b401c10351034074243c0189072601c40305500c0300d80101010f0b80b040425180102c0c915280d22014010103540b2000d440c01200544542140500755005280c0070104005140d4000d00d00c1e02020389403d070000a0700000c002c854051844094403a41e4200100300010b0030344c2c1c4c845c640c0144100b40003d243c20b1171102017007120380c441d00100b801c2d0380210010700c03108003003001ca8802020701740380c03007a03180d13040020013515210050801c14403d51903658003249507000f481007010642003006298142603684000410100a045103204044e152020740e06400f108402030f01c0c01d460341030b1107940c5404200d0341402500e500c00c9000c0c41c3c07541d452002a83e16035655010380d5003d5405031401c03510002542c241061500401d44c8880071451041000304001c0d2184419075158000c1c030051030f5180da0b05000001c02c400d00c100b45003c50340c0b22210020500719040920021104606000c482c0088081800f110114090803842c04440d8015103000c40000c103004c0040c40c00388041c1c81039401d241c07152108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 102229523 1250 102228273 102228289
    0x60d021201140c0901090510050720060a1d0f03031801030912020109170309060c030702030c07091a0a0e04080c070b0d0b01080a0b090a2403061a01020703030e090a0b 73
    0x3600800c40d40000b020300e059071b8004800809045c0895020103004610800602103200d0701000426029454111844000000800010590018051075a105000c1d079000b02007800d407540c24901580340c601e007545c45080c00343d0a006005809002580303012000f00e141c4000d030160800880c1055201c07100400064143d0340315480401d226000882c24511920b13001c0c0b14404140340303111401d0400d2042084a07400040c107580c11018200c403c607604e07190880102d0843c846da0000b81c80511400d2000604460b4070f5001013201c11850700c60703c0f8806c41800801001c3c04182c8190911050448080303400704038040c0c010011041e50000700c0e001c00d40d862041c00b12036002041c0035520980e60701e403060829600254400d520030b540082c1001004044800070b034070554050405190a03079204101e001807040c1d50881c0038810208200810415982d140071005081c0c0d10424a41d000035107171011300c940d400000c80106590303264540035079043e0040144103824400400d80248030780c942880d11501d841c1d043d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 102230773 1250 102229523 102229531
    0x1020c0102040b13170a08030705070209070206010e06060406080c0c07180501180e030304030f1b2a080715030605061b0705060f0901051803061303031103060d02120114 74
    0x41507100c01300d003000802451026403200c944081c01c0112003008203408204220788903442010152a52142001180c9900038008001d41200da0702c414007000c0d039000241203049035000c61001146694680600210340610720a0034041808000400c802c2882d00010384203d03c2140c04071035000365101b126415031380303000c106ca6512a0341d420062089903444201c0c0307000340c0120303541441918a1260180d40c1d03807100600182c01c03c4090003074034100511400e4008540403000046048001490800c1002d41a440e0b07000450122100c2d03c0f40d00c442100081c1404407001d01c005800340604d4207401c20305055142501c5003c040da500c80103d0155134941c098014841d1082108883c0f582050303c4a20b445600c2c1c00c201e01c00e0f1414407000b0088a0b0705000c8460380102860803e4851114510380c0800c0b02c002d40701107a060243c401000050141c17034040c481e000303020b540c0611120a2510001e0360620003601c445030044032594011015060a50609811411080001802500d0380c4617840c1600f20a403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 102232023 1250 102230773 102230789
    0x1d040203040b0109050a020f091306080607050a080f040f0828030902011d0f010c02040603060f0e061e010504022a100b01020102090607060b2205070305011d041401020c010204 77
    0x1500500c14080941709550303010f84061011880c14110000c12142c0d4012101d40510407890004c1c00341940c8140c0e0460700052081c43c045940c03509001001a0160b00a66181c01c00105640b000803001d001201c2c00c24055604451803010982c0c082d00d40c00910741c40514280c14949080504208000c0000c00030765269009580c00258a04944001001c041c580c09000b81083c400052812031035035030019980032a802400c04c0543d640c074520210300901090703480942290b103042414820009290002c1007441112400c2c3d0303165030b44000b00714510743c04004600c03416030041d0380144001d081c15802401503080d0390401d688145c280403400c0d00c2102c00920340d01c240f0382125203507110700c1d6080d000300c0c0c020810900095050004000100b4060f0280c031001424141c0c807031020401035210b035100c03e074028660030103850456200003041009800700384c800000191505000090100c400205055100200000a0f4080d19191201800c400c82e5414031600f6540c00c2003504140c440c24030041004010031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 102233273 1250 102232023 102232043
    0xf0f050a020f120c330a09080f030405060a03020910170a0e060406090804031a010f170c0427140709052203050f04140906040b030d1d04020304 63
    0x41c41030240a21814800b18055400e02c0303040100c0784004524030118102c20b0b00d662440200011001c2e280322a204543e2030160040840d24041d151a5002060680459114420150360305c002c4e1964030314260041030404c1e0000d00050015181510040081100301c0c5009810260341c400010450a0b02e400028040340c03490001d0703c0b0b8984061007807580800711074000c11422070ba039103016407103500041c0001d000e155159030f0101004401e0741a41c019641060000a0703175109800f50f10540c00e000c0c007403820294501540000c6083d504c0c3c404060300f103640b8000d001c03581c0e13134001407102808501f012080445444050b50720300900404100c42e400b40503003031080003401c01704442c5080012581110f128103062800700030b1182000604e014407000440240c008014080c00e08035014042e01d0f00d40c00c01003900003000156080a521203a00d09101260016075640f2244201f0080f550f0300c0091170b416810030b03003001e50705500501c0141e81191403003503840c0206018900040c101da0080f02d0495a90140c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 102234523 1250 102233273 102233293
    0x60203190c020d0e060c12091f0c03020708010513020409020a0503102403030503070507050f0a0c061121090102010b0d0302010207050727020d09060e0d0f0e0901060c0f0f05 76
    0xc059a41c000490040c5d402629060b10f00c50050b84408101c075031107603214400100840317251a02e407683c003482e230040c3c80000b03c0c17104051401021010310b150250300604c140c502c0465580010300ca01030107100308021a0410200541c00d2101810340d01200b40c2c3e10844803000002c150310180072003540c0440b0104001601090f0b145441041041021300e00f00101c0c0f4241c041c00001e4121007240c0e001003150030655295019490304514040c4d014669460350f0085081d0071080000300440c0e0030070360f400c41c0c8030b4111107080310003d550f031001c8840201046075182e11800e0411a444402007151100620000c40d4202c0803a0103e080e41d00d03003540c100c0042c1e50000c3c4940c14007500b1700090000c0c011982c00a040e141d42c3c180407200203030b501e007101265554000741855002c0d9003030307106103a55580508188180748140322499107440e103140342d10010a42c0ea482c400900d130310480c089003003800c0040c2098407a1b400c2000845000b929240100d03401c0700402c3c01480447c2c80c032071002541510681c01002e4143d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 102235773 1250 102234523 102234527
    0x1c0b01020a320303060a030602030c0408120406030c0302091e0f1c0204060b03011505030601110a0c030c1e0315020f070506100e13020d0c090f0506040b01020d020a060203190c020d 79
    0x7050641c0702c601500b051040c405140c2e036a441203400c49420140150300c0fa110340810704454465a440041e081c03207000300140c0894a140040d10803a10380361000c001420003500141c0692080c1100e0542c8918030040c520620800c40002c1102c18a014224218484030710000c50b450310300f165407040202184001c1c60046162a010b030784c0c090300a5201c614210751600024107204108140500c05220000c000a02c0c40e034441c054030079035000501c0071545030340318500f0a8a000e260a00040c1c031032201c0c5400100340240c0108158200240842c482d441d2a032035901d4800020078800c1c078101d480d5808010400e8400910400b07171420501aa003d06800d0030b02d21400c10842485500482c0040e441ca8100104000160380f644803403501511183e00c004050f02c0d082d40031a401d50040b0310700528004102402c4d08440d44482c7c03141340156030400140c05840016640c1d01040c0184800690200c42c101c00041c186401450b0003202c80c01c1d01149950021034420300741c80c1d540d1002d0700141c4c042801d151400e6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 102237023 1250 102235773 102235853
    0x20606131b031b11060a0e010213060509010306060306080c01030203100b0c07060807020601052805040c020304030b0c04080a1b0302060f180f10030b010509030f010902090a021c0b01020a 82
    0xc0d250802100910940361501c1d01c1d00d100914810860b591f03016510700d40c840c02e40484607401804e1216507203590301c400d0041e1980c0c0218903100d000034504080800d2013800f034403c50041d202c001c0010005c1c010500011000303540b005000030303419526094002440c3d103895001d4101e02c85a000030304400c90a0940003010800e0050500d0b08552280c0c00400607a160181c10580c05041c1066298010301da8440300480a60154030035070300f141c50f08600c0c54041d6408000b410589114110220280d11a80d550f00d2141c080c1d4080c080007038000701d041c0000900010388481822109151404109a1fa9000141d464015145110085d4400250b020541c06011b501da4070800046807030f40700300a005800f040e00c0d088848407000516685415818040e8040e5042e16600c810050446001c07455030a20306018200c00c1101302d010304c411401164000181c0d00a544031078034031007010100001700c0318400002e024509105c0d41075028004d58900032416010b0860701d601d01b074601381c01034408204410241d503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 102238273 1250 102237023 102237071
    0x10602071d070504030609261b030702150a090305060406060e01050102010c09091a0a030f06200904090c080a0b01080f0c09011806050a030f0209070302030601020606131b03 76
    0x60240d840030030403881d400c94107440582c5e4110b58002032450031031600c03c001a88c40c04400780c4580d500b1015010520090004010a1a44211107208085122401c075a64017952400940c4144080901c250041030f0390301a040c1c0d0b04441c60004002c44c5c4d00c3e2940d90501c10255401e87e14036842d000140803010a41028500400003031008104412030020700030131510311800b0340e40c40680c407040c00c03000c020258141e07208400710040080301c0a560740c2c0740407261000e00c854204c40b100d00700070126418800d4681d04603a4101c0d500c41d014030b03140d450801c201c01000b952104031010764400601250b0400c04200c0c100d05648107905012495043c0000203146c04030185d09001d4581c0615521146601d030041524110390001140000340d0300601002400b4098035040740303401c004440400414000840172801803140240d44440d803d03220208100c041e8801216a1405a4031803c082001c90030684620b007091821100002115000c0c0200c200a01c0c01d145040d900080c4c40c0c81c4040105490070121040c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 102239523 1250 102238273 102238319
    0x207050114160501110c010608070509131e0f0803090f030306031510090905060a060f050f010f020f1605090a091211030d020703091811030c09011701060207 69
    0xd8103210004910740d0720a003400c0031010548540e41d0010040c0035080324408802c030314607507034481440500450003481c0a100b0030100388912040001e842c240f03c0d5185014103100807101c4081121915040c40301d078890790074103000a04400c100800308012004071443c41e0311603480d80340e9030b0400d00020351402040203610b90040c4c00030802c2c80110b42d00018207a803203103d1194503903910783da1120b10f10319180055000304d0115041c10041c4c0200140443d40781d1041000b0720040150613156035070303580f070410240151904128029001c4000e580035442c08201400c040c81140e04040d441003c841c2424803d03070550071004501e890910a514180c0000e641c000e80f0480d04018100031512041110481e0002800c180819100910401ca1050048a02d000615601955910194900104031381c0c2d142c46030101105803c00c22808807111401040c56002084030150305507203880c009941e440d4400001507040c01034a0300c0a04461040c800100c1c02495a034010700b8813286402c0c1d03110f02070703004400100ea03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 102240773 1250 102239523 102239537
    0x9100b0f1014040602070602070e040503090d11120607030c1b11060f03280207050a11060715050f0c03040c06180801051f050f210c0d05010c02070501 66
    0x401512104a400c054520840380032604040791002515405000c0714540d41c01c1c04005000300c1c000340c0016010303088070195801c603482c16a54044642c040c4105440080058000304004081c5141c2000c0c00d901f6940125070b5030000021840002d0b01c081e01d00c4440c6406a080b000400ca010b5416100d12900c050721820988047c02e01c40300d0070888010044d4004080d19a04080340d5405d85409050715110321103c0c00d62175580c00c141807501990072001c506a40e86064607503081c1c1c040b81d1540203413210301e94408010051042c00c0d41c2d801d079004207500380c500d03003082003408002c001c5103040394004030544801000250360b003041400486580e9009107600c00d409001c00a1200042400d5043c40c00c8904501d032560308180301590100000f015a0b00c480c4a40d800e090034002c01c103141302000c82c0c81e0008110031080903a606c0d0103010104543c0034070b180c4d109a01c2043c0c117582290200108220304c40038000c0c1c4141d01c110070001103105010300380648541c0e40d90058200e1f465010010074000d841c090130612 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 102242023 1250 102240773 102240791
    0x3160810020f04091a090c0403122105060303090d0605060a05010c1709030109060603111009080d030504020d080304050a0b1f030609050a0c06120f02030108070501050c07030206030a050910 83
    0xb140c1403085110b4801007564603c010032415051840300000024001c2c00c2c41310718103100b10084403941260000341c0d00082c1c211f13a1a1440c1d40150b4142564a48240101e0706034002450004001d000040c60150140002c2010080a0381e5407882e6411152144100091034280001481152036081d00003905110076021003001180454253b1b031030340070745004583c0e558400240460b0141261040c01010b55003443c0f004003c003c0b03036210f50014814280c41a0303420b541406012140b051b058030407013101e90085000051300f0f13442504510350003070002d48005155500f694a4140030360007110140c130990000e81c00300082081000c1c0aa4002d00440d482000703030305050044c0c140010052000400080d42c8a0011003000030038425a48100c3e0004c1c1080340302ca81e41d0304080c098141141525141d0351607c0401441c440c458070a0381d060b80c514200505900c0d00b031900643e929032000b1501e0016100d000000801652404c00452240c2044007001c02c01d400c049001c1c0f4981181c0c031015000c02801d000c0d150b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 102243273 1250 102242023 102242047
    0x504150312020111031008010b010e0108011401020a12080907140a1809020315070f0507051506010203040e010623090102060703020d0f0504050a03080105030d050403030f0504050316081002 83
    0x520999420010319586508003440607801460714203008075054402108101d03448016090130011503030690b00a10011003441c0045400010f114841404100000014007030360b4541d01130307402d0121040c011540d010f0303c180c55140d100e06a06120340c0001d91f101042180c2403809001da04002c0c120720000d4442d0156540028911200500a50a0341620414009032070f82180d00070002e0190041c05540a01d11080b034421b40d43e480032a0841c0c0403aa03014441481240715208a5a00d1500702b005440024880940040701100261400741144000c0c00041402520710000703900a002c1070b1113126540d001010241c400089142c24507250319018024100d8503600031503440d502040c03d00c2c0046e5148c800c4107808000380700e030240310454203251008210401c140000c8102d9028000e443d000c101d0303030fa070714201940caa80e183c80174000120103200030400240140416000c2c0540703800c1440c241038541003c00d281c0b400135480000d800404510401c0400428400c40003641141001980f07003464001003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 102244523 1250 102243273 102243311
    0x140d02130806011d060109090c020c190b040302091305030c07140103020403030509090c0d090302071e050d030305040609020d08130602060108030a0c020a030803100317090108130204060b030903040801060504 91
    0x800b1503150883c400007605c980c41000c0ca1006800d051204100c203054221000355294001d19096011301c0592804040764403080d0150421608900403031441d103821a400d0024142d800b40209100061b122005800203205001408580c0c24000c020070100d1b02e003072050b4850b0034240003058103041c03040000380003195001d02111070b42c030340558004c3c481e602c0e440c001c403802d4415804c446611624041043d000c0540c0418140201c2d444032000302c4410740c410071101c8000a05104441e40001e0a40f140c10002c1d00075044941c0c0503000e400001801c50144c1c0204484100400003150742d00380001d10004400d0b4500340c0705000c1c00d0b4a02c01803031903604204031199a44030310741c0c2032414403034030408070350455560f40c1c0403501540d0700055803501c03414100c0460b900d00c25030b03000c00c6884148600788000000c0840c03040e100f0b070f00b00594444d11151900c00c0301d02c42e01406400e00341d811545458002c01d4031041e44009602884908000b19900c03460000c41508591890304058800c2d0709010101805003d4404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 102245773 1250 102244523 102244559
    0x50f01050412051f0b1201020f03011203050909010608040213050105091f170a0201020d0e010903150e0604030e0a0801110307180f030f02180613020307140d0213080601 74
    0x1010010001414004d00e401d002c0f00e030710950042400c0c424074880c07106401a15403800140d45c0c0c01415010717140f50909038001d601c5001c40d00303003091004100c0a01c0700480f1602c5075000c1d045c4246003100d10b00c04105002000d800003800301d040ca406000031401c3c0764410940c00070705448100090f50400000500c84280949004100c00e0503811303101c2d01d600d0030454440107001c142c8142000360742108644c0d4590440000680c0035020f079100c11501240541384e000009c110503902c00050341e084d9a41d00c841103500e810714030f0711140d482a03400b066400c10022340d40614000e46480b4100440360040061180c0c440e04001c0550341080f00c203104901100080d25081342d1b860402031a02d050b89038802d000c45031550700400f0400b2240b14000140a003440421000a00076a82190070050505400303200390025a85250024440da980d100d0008656000c2d6800103550302c1c240241c0c11038031030811200c0c0c000303004407400103030700003234400c11a12940e10610007000c2d00c8019004a6252203c040720f601401c070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 102247023 1250 102245773 102245789
    0x7090e0f010e06070207050604030510020d0e0607030906061e090b1801030c0518070206060d06020c01020403030504080c1002250b0307030c02010507110703021333050f010504 77
    0x811144040a0140c810111000c500070844104010180c80e078030041a00c5080150080020115540c280b100899055031782060040a200504510041c004d40c4070983c03d20209603912010952501c003030000310700808180d42c1c00f0800c46420306040080fa00658001d805540e1100300090301005a90601000c0740d880300800501411203601060200d160319580300d040030802d400220412200030840425202c0a58101c0128545601d04150400d0300350341440c003581c85000014011302d82480040394079403044e1800b5050419100085003681c104e43c0045000c00c002084c00d000c0440104440d8800c03031401c0316550031001c100310001c0c1d103c0a2a07030110b12aa550b102e4056003c1300c42040010042c14001d40c196a6854005001002000060714420040d42000045a00584600148104c140141e0007400c1417510b19400c0000d00d00160781c40464868650300b0000100043c0040c00441601000419800140120940c140e4400b02e812041c402c100700014808070766407102c01da070306460b030300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 102248273 1250 102247023 102247031
    0x1006090302010e0d051203160207060c14010f0501080c1903081204061103040b04050c03070501020d03090302010b040603112b020607240209010e060906030a0209011101110414040e0709 81
    0x220106503402040d6401403d14801c0004180e1400c00c100010340c4551140d20b140350f041e0380c48074820ad0303c6190302d203c0c2d04002841c4000320740c042205e000d084401020f019000007800e03007281c80d0140640308240e2004841d500060f61000e424104201c0c40403a80394078041ca910301c1411680c698206000e0749401c5000c038060000040c04200c0c83d6403000f00a9030720b030003070540c032803626180080143c001180c04980c40c0c00781038040a03603400d00040c40016100140c01900c0780b00b811045c01c4008005000d4141d00719074035103e81208940b268482c4002039800b071051100030504050500240e0450850141c00a0410760800940c881c1843c80c03421810350704036825561045507003002403044207242002e41d03925940c8168000780030b41c07a50080c00541c0003130b207e60061100b06410000e40e8010203900c141c10010130400580c0d5441241c0c020310001005041151140c4a040507680c02c61790191800481c0c400001024440004a05040c51044000b10f03400d2000d012050102ca448030143d1240580c1381e03450f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 102249523 1250 102248273 102248297
    0xb13090b03100603060203150f0d200409080904150e010302040b0d02040513060507030207110d17030c0705010501090908091003020d020d05010509010501021c0c02010203161a100609030201 83
    0x40c040d20505042c540418000140c881c144140254130035220425041c00365000300c891410915803140c0001d8004001294a900e25102e81d100084441c0d80c40c00042c1c40300140c0c61031503407140f080020241c081d03030b805500d1701d846006000c101c404000350580304004020f020044101c82010482c1902e44c1500c000ca420aa4100403c071483c0040c14020342c4141086c040007088281c202c039001c207482c0158028001a12083d01c01d4049200c0c14034050440d00c2c5607000c059040c1016164000d400e0b10500e00190302a80303840a5601d2a0000d4901c8120399030002100400d02c5000d009940c054480b00404001c031390309980d140c0d1801d218010145004000b0380943c81c000d00d020364107489103a44a0038042d903171921381040c244018002400b489124100010001c03800d94030004009803e81c1d04074100318090310500304107590b17030004140200d045102c2082003003102c401d10301400c0c40c06881684503c164120b8940044070040740100350b107440e0494107030100302d069407059203e401c0320380a0815029440d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 102250773 1250 102249523 102249529
    0x3040e0705070c1d04060f020306030304030609080c0102070b09060a0506060702041e021c1a010c1b08150a1b021c0c330615080a0e060708060a0b13090b 67
    0x79038050400c80c58104070040a02c3c81e02c41213240b00354810b81d0f08001003403685144000f00d010941c3d0f2590160b109000074000224a54041d00b0f0440c0907903d1079041107004c2c4426400da034800c1008480034207c0c00180400b01c5000c016203504a620000140310324586031021848900602c907010740b1864a0f015150380b65070754500c00521036040030000395a41c0c60401941038275500501e103501007103860610b00c030480d006d42c005402c840090583d629546128681c8038900c00c1d1481c07822900345200040e00018080d801005284042c0300c1d00100c16005150981c03140044585640998581d1818001400212607000c40d0600020043c40c1c521040c0e00682d1004884211020800074248180000701c030103188448115424110b24105040c02c075802c46589000595101d840b89211000b014080240060301800b0001e50192400c1000506000403058141c6040b500790750308008a80901d06024060414241180c0504000040d0030310744071506001c40341800862040000c3d559807002d201007155 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 102252023 1250 102250773 102250793
    0xd0204020a0c050a11100e06030106030b130203040605010f080c2209021201020c07050a0b0405060d090204140103060615020709050408120108031c0c020c040504030509040e0105160203040e070507 86
    0x2540120072100803621394a8000c0403160079000040c4180b245040f8012618031a021300b190010b0050305103800d603480c1003420f13130140403489070239a071102d0700c503800003840c010300d00c0a188030380d00941c0003040e594503240a07400d4500180c0c01050071600510300040864071a111046c4580c0502c182c0200c1d40300135258000c000309109400254080b44584902407417420540103032010340564000d943c1c090f0354403010403100e040b040c0304407182c0b84014070080107685403040181409400b900000f00c2c07030420170b0b40054220f50070f808070f03020280200c0b0014000c3c04040d210720b0700a800c800300c8180c0696124080a0369554441c401c40c21101d0322400040c00300310720007003030300c1c080d01d2025030f01511540c4800e4520b03101d8100c0f804410710881c0c0620b44c0101540c0901801c540c1c0700c826006040c0612038041800050a0004c0080d020700c41d003004040d107591924803e07001541840400061b16003020702d1204a44900300e20710300c046500c140400c0c401030602c4261160000d203d81056503944003645400d414070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 102253273 1250 102252023 102252047
    0x901080c0c070305010b09010e1e0405010f05090a0c05040b0607230a0f26030a0b010207050a0b04030312050405150a1401120b090708060c0a09030606060504180b0d0204020a 76
    0x82c05203407000030030050150045081180101c5182505a89403c2030031030020f01120080d81064040103110760841902c03041940144c042c0c03002080d5916008205419140159200d005640c0416010414010046241405068216010700c0418207000020302c81b80038012011348280c0201c0b20369926401004181e5001c184800c0c10741d45403000d1400c01c507074a00624481501c090b81d0b0182c80c0c10807a0222110b803084802c108140340e00f180c842c00700c0d0a000b41903414480f030640c03141c03000c007042c20399519a070b2a004101689070b2581d10350861400900071100880c01c00c0c480d60400c824400042c1001c104442011840813000500707a45104000000e00700308020f0801080f9010b00204c0e02440c0c05904111040c061080e1403c0ca441740300702107030744080310700c00c8085980000011070021281980204805409440c0540c1c0007074403901c40c03030100c80300d907403000004c1440080c0c00c20403101c00064180c001c0340340070810442c01200c000881c46404011030002e118650006101e500d16024284601362 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 102254523 1250 102253273 102253297
    0x2130b1f091208130f0501210e060907080d0305100e1915051c0f030e01090b0315091f060507060612060504030206060f01140a170a060f0605030c0901080c 68
    0x2c801c0043c104108141c0c407058001282d00d0503118007264140b203007002001181c9040c1c3d92032120240094480301038013122444818544e0b240c1070300c0031600c0070811409000f070761b81c44042c04210b0300d000819458240c5540c82e54081c182003800b005140704040c41d60904035031802039885400c0e610381748040181035a550020105511741040c400d122142c41c590354090311000c0c0c035031086a540e004058003c032119140000c003154208403074070001034403c80c1301c0411594103040103141c05480e10706c4d0b030a0981044562132a46140400b5803002860694001354108070b610501000390000d481400c0b440d6066400b03042c043c003030000380311010881e465001e0070092085d40300580d0400d620345030180c0500000d550941c014880c41c008515a072500108840c10710105844082c50b12241d01c131201100d420520000c000d21040c2c01c80c004124510f140b040f88201d0544800088042c2000020a00c9a10f203421506c200003041c400c01280e003030010100d8480c2e1200342442d144580d1403030400740c881c5c8504200704c44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 102255773 1250 102254523 102254549
    0x40e03040b04090c0f090b03060d05030c0a06020702041406210705040c030509060705190c060e030a0c05060f19180212030a030b030312070f020c150702130b1f09 71
    0x285400c0d4507440000b40d0481542e40302280c4400041c11201211b8a00032820500070401c0031510302d1400d58030441c3c4070b6101d602682d041100a40d4450706048064400340c070085d40008041c421440c05118200c04a0b100b101002c2103810b00201285800b005005190f543c0e100010f04403e4240003004030074000c00008000703100400709060000e01401c8140d8024106120304004164500e00480135207030242e400f80d45048504030031201c22100004024020f5442c5aa074200c0066a080b05000420710a5074649030b445400416260841c94850020300a080c640242d00501080051071f00705480300c61440074021907092141c1c1a00301000f0944c4c60000d50180c01d20200807154200071020305008000350b10100802d11141003419140e1180080c0805140703440380004214601409101118185610403103103408a803001107005841110490640c40002045070021850f142c2120b800c0140c1c00d00c414410303507015101080d0300100d60f08a80d45030030078008194000510511800c8010301910038000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 102257023 1250 102255773 102255779
    0x615030309090e011b0309030e060d0608060702060402030a02091e01080601050a141f05040306020703030212160207060503130b0f2203093003031a030708060402040e03040b04 77
    0x541007858a10406000c98141420f640c44488180f20340c41004054081150680b41103180803401400d000104030280a80c2c0c41200700c9544840002d80408a855040003c0301401e1030b0580385003503002440302c81150700480810006840c0450490401c6138107950608007034550a609062107101048440d0041ca229000083c82c0070000a907030741210820354003980d8254481003601d00d0500c0d4a11413030f4010300d40355080710082c055507007010b000403103502d003040c101500c1756281820b0303900c400d6094000a801040c61143c0c0d05038031540581280c550400d0300285055120065110680c52041d0000d109011002a004c42c20900034003405641c040c483d21058079220313504035860581503a0720729110399010b850084031000152040101038240c1c0703920451a1800840d0310382181c00084c0070300d200c11100c014048080042c024001998841d460101d49881242140200d514110b416035110b0703030041000304043c001c080350300354102d50155000b01f100910300b03031032038a50312a540c480d07500400d00140c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 102258273 1250 102257023 102257027
    0x503030322140d02060a06060e030307110402160b100603050402030607030e010e010f0603050f0a0506220609110123040b0c070f030f03080c0f0a120605030304091e1404020d06150303 80
    0x310344200d00906d0100111600c0e420200e48184424803a150164810000000410405101d02641d000010005803030128100030070b00c0300c0c4040e820204e921040400c140720100a41c50300038030181c502d03450300f01300500c2c2a800080c3d46000c050301582c1415600d00318010f400100303401890b03001d14140002c3c0040500749400c20001d255910050350f03180076620024208507000b24204542c0e58000c401080c1d00e0f01c03001c600010300000440c24055590340c03c401800002c10501a036000a13016503044941a440480058080d4012841000c0c40b681031140d40a40b004400c0c0651782503481644280751100c402007801d900d0300d403c60300b00714000c0c0807591000040180000c0c070f01394000c1c401d41d2100d101b0744401d0480b05450107805204ca105000500c180040b0300d01c03603292004188407030100821900e43d030300d011900f56482038201d6101c16440322059001c80d00060201d4807802c1c0f008008120380801105011042c0c43e000d08000c0c4a01e5124000009220702a00700c45081c3c4400d031240401c2a40e2440c0c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 102259523 1250 102258273 102258283
    0x30a0b011e05150306011b12080910091203090204021201240f020a0f061d0708010c02030304051b18010605030a060501030e0a1212021b070503030322140d02 69
    0x24020074a44244400700b86030500342c07070000d0310800c40510743e425a12090010b4075002c100c0c49150803030072800c1c610f03c40403c0c1d0114000480300d013103448000d03142c2011403040d420000040d00e0904081d050410f014006036020302c8034648140e50b49070000341c0610038400213000e80300b1860071499a101e540d00105040d4541402c02d01039070014046804030003a4550192041050006982d0158000d03685d204c020a2603900d90701000c0d03210341800103210386101b401c081c00c1008602400000d60101006004d829024800c0e403901c8034542c00103504510742a601c0d6650b440f000c01a009031a28000e046000a8990040c101e44203400003840380c2d070070368440f5801829600102c4100c200b0301e0402e40c1c00075165001e0700c24004d1101e83d050140c10394181740c3d00c60404443d00c4050b1030081058141b4100d207070907031601c0600840d01411392118007038190004103516000c0715400c4548070341c00401c18448e502e0080b00780d040b44801541482d9151943e54104242c1d20783c1e03030445007a01c0b806000f0400b40380d40e0340810303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 102260773 1250 102259523 102259559
    0x1e10081014010515090f060705060703090308181e1e0c19140f0f04060308040e010b03070f140913090210020f0c01030515030a05060702060903130311030a0b01 70
    0x144041460f0b903600100000e2250304444a000048100100c0c402e070305002081c4440c410016104510b0928655039403844c0620440f50b00000907a6441c01d1010507a0181485401c00c200a4001c01e0703c151626542e40c0382d09404500c00f04030301c0c88001a040c8844107101880300741d001c0300302079107006400185143e1280e080b40b01e00b0b449601d80607581c5a110307003100405020313203130110000d90400d01c00c801801501140314121a034000e81d6840683d446641c0c5008900c0514810014036450358a0010b5800820b001a04104882032040c820882c903282e2040e00020700c11550310b0f01c1c900e10048250609000d208a2031559005010940e040c1e0320420b040c1c02c0102001c0c403e5540b140202c20300c41040362a03102c00108208643c0000d001030314650702c03a40141d41c0226401c507000c80b44841c1e0400287c64180c111208403100c0d0024801c128540790103009055120141c400a140ba1601c40c1c1c8a40100340324038000240b0601195040f403080707840030404e81c041c41e0750040c0c480c0070650715007007503209060561b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 102262023 1250 102260773 102260801
    0x21c0507090e03122a160302100b030c13060306050a0209010f020d120f0b03010f090308150a0303030e0c03010c021c03060506031302030a120909060602061e100810 72
    0x503050054500004881d52544c40c208200c1c801d0300d40d1503c41818030361100c2441980781e03090546518002d9810020105c00700948507102d6156401e28019003406000402c07a2200391810805043d25100402e907441d03079a0003200c2c41c00000c0c400035401350052420b60000b400312858481080049a225402441c140109883d09a51812140d00403a50380740c1041003240052540d070700d6001004060f401070051041000380100e1040c5641c000f00e07085030301c0001c103011400d480d101c82809050f006034266404c00d02140c4110712600400c0d010030f50403035a91100404043e078400740f0410044040c40402d510034001402407001c1c2c4206000295616800000700d0704810591041600f203074064401c4034111540075182c282550b54180d0342005940c1c00c900142d805024007502c03040058607600c100c14081c1c06a031919524075040c0741080007228030b55000322007036612820034480e0010310507664000301c0d1030f1004502521b80d04d00c1200c0244461560081c040e5100342500074018a00030340110110b0b41c591 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 102263273 1250 102262023 102262031
    0xa0b0601080a150902030a02120907030b01050307030308160504120b07020d1b0f0206040e0705071101030b01120c0207260609070f060507030e06040b0705060105010f1704021c050709 80
    0x82281e02d00700e802c4150550384011200358104500c66440d0040c40d40401125001400c000d203c02d0001c21101c003c0b2409030440c1c1160006004100d82200014058031055000303020715401e5a402400034034028101880003600c03482000c00c038a109a00310780203800451450346940005150411710700c042074940070702500a50750100702d00e500ca4068503000c3c0001c44046418030040352641200400d01c1c400076a000502080080342860108041a0081c03070150365140d56010941804414030300c4112140c0d04160504000d45030707580c0d1020000702c6203401d0541c00540c01280002c2030f4074180c4030790300000c1541c580c60032143c400900b4150030044545450140c03610341d900c040304980c5a1030b441c002d004007245010f405020f61440b4001500302d140c03180c101801b1102009002500340d410076400300200c0c0300700044450400a040c40101d00408003800c1c041202c400c40440030305880003100b4a1305a00098800107000e642c2c411a80312000742110729000c6950031301c3c1c01d110307885003900c0c05052011814 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 102264523 1250 102263273 102263281
    0x90f12020d02060a0c020d1b081207020d0513050609040905191103011104060f02010b13060503010c090e06060a020309060c0102030405061b0421020406060206060a0501091206020304140a0b060108 86
    0x2280178000d401c2040740d0183c4810050400150764181c0d0540c690030360441c00c0a203020000f0700190041c4a104195400040e441c82c0515009141001d104044010883c0c140018003064090b04265170aa07001241c40c1d644501055022400410042c00d0182082c8140030020252050004a28850b40d02030946540c0c0f00d540070081c903080c0e50228903c00e0720001c04110420103607202306820400148039200100d11548a400000ca100c1008426442c07120750305c0030b041246140074410030305924107d044c0081c555280c200c49914854008203898098a030000e400c2204070720030300c1110b02c0d1140050002e40c81d1001c4810740e9001350000c0b01c04440b02c2c8100404518007000c000f911204c410801c256061500c0e080c0700580b9007040f6005441b20004c640101500b00580d1a4065180074100070790040800d4035000013001219041c50f0f000d18180a410031003407084006034140c2d81c1c0e4050300090b008d81c2e84e4a56140c9010146080710400c041780c0114440382d4104400c030340d00030780549000d0340c4030160364039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 102265773 1250 102264523 102264541
    0x20d060f030503030a15090603051c020d0e040c0905090c040302090601020f060403050d060305030d14010f0501020723091303080c09030a1209050d03050903120f0a03090f12020d0206 80
    0x40240400741c526802400007078075408032171b00031161951000f01124241c6a85d07042c2e01080c1c450b541c1045410390071a0804105e2450710a04880410700366100905801a0111002d841f0060b520704050207191a99140c101c4103000301e07880002040b001d0140e00440c0341c0311180d003030fa0340c000e800224440c500000200da41c541c800079180d03189040c00005003413180c031143d90940d903d43c062210324580649a40d000004a20700348081c0c0f911401d08040414448080820070180c40d005802c1541803002c110700501007643e001881e401a1180e402c0b65030050811007025000b00c101e15501aa8400480000c024503240a00750303a40d152886502c5002507511103100d40a0f0a001c1c000407660103600024100000c07880aa052840203406410150840c42c0c071803002c03500d800403000c026008120001003001c0141000c000040540c1038081805040040104618000d803103508400c004064a41c00c501d01032110244810307001590280036024040700010307000e901c8560442c1190094000d002c0040c0c0440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 102267023 1250 102265773 102265799
    0x10221070501060801020c102c0609100501060f1d0a0b0a020106090212150a0b0a030b01110601030206030c0a14040f0801050f0903030a02070611030f061c051b030a02030709020d06 79
    0x1880107000714072140d00d507403402420340701c0389503911b13010010270101000130204809030386801d510301510681c038101c41d1283ca409414594204103900d020010004c2d00d0f4450900007040409240001605030402d12084504450070006c6a0082044c20002240c05003500103000140d403e80081c02090760f90442c01c0100e01032140e015003110303500000251a0705c0b0f002d044000c0224010016110f003500c9210340d65064100c039200c00086a91002032044560b00007001d00008015500100741a6040d9404100c840c04050202c2c2030500c00421324441e018050007140c03982003e1940090307221070703541148900307141140c4599900c552a11020401e582c5005000d40e2040120800071480d549500400340c0095010500170794425035942040300303818503840010350282c003009900c4030440c14042c1c00c010301b600c4e004240d540f100000c90b080500103800400c41895070441911019441004c03240844d00308051004000d41c5030240d0200400e210205a010308586502d9980401c0031a4a4420307a8a5403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 102268273 1250 102267023 102267037
    0x3121d120303181c050903010e07060e12071208090307150c1202010203100e070e0901030c030606051f0e12030d060f050102030a020a02041d0303040506010504050a050609040209040201022107050106080102 90
    0x40c04804c004100c507402039006045080003c0c00016114032415803c50510f24030b82c0010000840c80014945149040d400442051522001a0490503d4000d44a41d862840f0384001c0501d0008070b601100c540d400c1c081c100084c80c2c224441212440c4883c1c0043c191010704c40d0446080d0307200880062810300c144266031085031000c5038017a03200e00b0500d1a20912400034040740401844000c2e003205a1120303044039009503c07801803051070300d0441c0b03040c60940340a90412805840e030300c6038121440643e074000800500403410070182c0c4021134804a0076904c00200200307200e10000480550403c060f9011404403100004a2004c0319224401261640700d02841c22005034081002e4102500e0715900044142401c90444060218040f001c1c0c0d0a44e001110203880680201c40100038600741801a030341d00c0310401004104928000000032024040644080d00803031032a130000c1c0c00c590003009810100c07181c0034810400f0015410b0180d020303610a0706c0c125515402d00d800056000014000d440384 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 102269523 1250 102268273 102268303
    0x20a0b0c06010609030b0f1512010912020a03050301030803040819020a030207080d020d03051801090c060806010903150c0c05190215040f0501050706020405270f0103121d12030318 79
    0x11a0b200c01c4005203400d01d000d40b03042010407901c03d00107410f503100410482e00714402e0f80082010807440c0cd00110b0004c0000034a800e42d0403e00344000026030107012281580e9202006035103d0311103040200700f900a40b40792542c100aa90f00f400d80d81c41e0009003c040040c8a60f08941e0b00b143c03148003254591121002507405039100340040c1041d98001e8202c2940001c410029003c0c1c1e0032a40109804c0d5400c081c03090f0741003c0314104c00d0103d685e01070b907520341c055004e0a08494451540e55202e800050301140c0b490410390320a0a01d14071392280310310706111340c0c10034200e800d0116038082c000f040888210b0120705c910790190050000c0380e0184166422124a40c440c00110703807600005403415440540200d81060f4204070105240e581c1c0200d490360303400ea002c2200c1a1003c0e0711400000168060401f2000c0c5082400400000314488402810340b40340380b800480728943c3c03140941e0300c100c1182d50283d100e4042c1c0d441040c2004000091849400854105411a5070f605a07041e2140c40030000080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 102270773 1250 102269523 102269543
    0x2030c2e063f06140c070c06050703050d0504060b01110606030607140d090803060f01170103020103021c0504050d0f090e060904170d05010f0b040b0409090f020a0b0c0601060903 78
    0x30000c41e400700001e0001880c0141c0480b1407400c04100b11080d08112044941d42c0d62403200341218001045425440600d044459141041d29103545a99811512400082010000f11036042500c03500a0f124540106101030101e42403504c1d00350058800500e10301d0000722049040f440d100c000144403400344034094041d10035070700d0f406400c44d00034a04408810190b407003000b80402045451080b403400034090482d840e10390a051080282c0c4503512185c00341048514203402d9040084110101e044913424200140c1d1000d400e583c03040c28802d4400c01602c05840d000402040c4440814a000f8000c441d42e910740c00d01402410649010b40039010b0b400b00b070b050100015101d800c1140030030750028080e44000402c0005811100b21a80c08090740040140c1c9035401000a5600042c040014042001c05e450030a41042081d101d10b0180d8030610003810786400268040c440c0512201c2120703600588000802500c03580311030715030f038421404080300740720300b000004010344100048000d0760784c0007543d86 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 102272023 1250 102270773 102270809
    0x20f0c06071a070903050f0a0201032a0807031104060203130e0108060c0d0b060406210c12050402120111040303090b070f0f0213051306050108060105030c1002030c2e06 74
    0x802c8050700104040c0503c200c954010011400030059000e510440b4001821040903d100040540d0400c0f1441e09401400742c5100c400092241d6600f0f01041442c80d1240e2240e6070042c0c2200904a00c404265075800009004940140e022000780440340f80145503502d11a61803806140c3c44a007440740c0c00c4142c0114020034040034120707006100003000320201152020340c082c00a0703034942c855440300c008520301c0d4000c0c403400e0200c1d00040302d1003008007030100b100100301c4001908110400d182d00403902ea840d400201195641c250003031000c1e800b417000b0020000c08001200d49903019020a5001c5400b01d507001411015180459110701c0c0e00000c41d1181c48882d5492103262020840304036841410060300648a049a1290a200d401c2550380d4400c1c00040d41454801c90700b041e08400040e4011400602ca1600c0002d411070045005a41c0310901c4044a03100724210300400c5080a124080c0828040a1180702c00040301074002c400e500c8515107900d40d0815040390801c2c882d002107000012030b54 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 102273273 1250 102272023 102272063
    0x2010c030c060603170409050901090b06010f02120d020901080c0405150d0b032d0a12110f010501060c0c05011706091e04380105060d0f0507020f0c0607 67
    0x456006449042e0103e400e41d129559007030f005180c0c51041c2c290182c0814104110880d034084c861300a0f5551008200e4025540c03680030400c03000170825414028a0040000030070301c20401503260140510626442c0e203074044100019500803d041400210b194021913810300e01d90f41224215030b0010010131071040901e00100898001443c0c000550396075100803041520103001080c0c51840005402c00b20f500041801c0030b42d102d603035200c8000f0780d21a200c40b80019100c0541c06480c80390b00d00344070610603a8060030341d00c3d107016200d28222550a0500008020750001400c1040600c165001200309444200440741c1400e45504000e0a807940b201041040c00e02c144d0045e00403411000500403c0380d4509000c691141c162000c8132040c841740790384400c421181400207002d041c08514160a14440e8002e00e030108010b0044074814600011001c0302080303658440007032040300345424405403a01d010b0103920b03031100c00000e42141c09507207080801854441c01f103801c1a9481ba828a81c91301c044c10803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 102274523 1250 102273273 102273287
    0x3010e0f15130203010c020f060a15090b060c16031a0403050307030902060c0109050a061b12020306060d05010b03060901080f121b01060b03040c081c0513030b130b010509010302010c03 81
    0x300c00152191950b0351409600c3c00c2c081c0f05000d03003042d00208605181c1702c00e85441c10000800304004a80b41030702004c812443c40703406208458042e0000710304004c4100000b1282d115010b440c1c0306620908140b5404810920010000c59004411407204000d01d00006107900204071030050001b9020000103640710f009a101e041c43c180064946414107100040c0c582c2181c12042c0140c9040d0300c0505602c1c1000a01d01629045903003901007000188554000504025100042c0c80c2903180c01000180c4141c0380c03d410380b00b40703054031002070101d035a480310f0640c110303841626030f10700074041d0318004100f9800c00110b0b007a6190740440241146a507116040c00355801a801810400308014150040e142c004d006010281030f990301800d0f9241041e143c01c00103040d084c2e00a000304c0d004820240c4900c00d01c8050241d41007554100551349800c2594410703100f000701d800c014a05d0300690240041200054402500070b803188003c0c040341d90301c5404000341101c0920001b4001030301100c07154002441406 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 102275773 1250 102274523 102274531
    0x3030311160210090306020406051b03040303050913140a0903020d030e06010501110a050d0e1e0102060f040f0c030b1005030c0f150c0d031b03052403070b031503010e0f15 75
    0x40d228012a07100e60b10351b01603a0196022900007440410403010518000503800c00e018001c2e8021840c0c03d1969401030110700801001e00d10030320302d00041000b010120b800180100c40300d1040845030380340035010140180315801c011360040c071801400c17407000d0740680302e117024024000000303001c1c0c1c2c0e103041d00444044078194030303841440c0544180c4100203903040042c003901034403940b903a00e5218100c40c2806000040d44e2648007030103051000030344490343c000c04c41170b03002240d01d695140169100d01300310000d650070400041c094440800d000041c0701482611502468030714803000c90440d6602c0c2096940c0b0002000c082d07000c1e044030f141c5515440c00300001d400704c18070860882d08060000307899a050508035000440400c0d1a0088030308e10381003982100550700d4060804100318284020190108840a1600e241408803d0341c03041c169601006000c00511041d410150380780341c1051403a070060b5110300214000d6081c031002012005021441d100301e2559900100940e0614141c4190340c140094 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 102277023 1250 102275773 102275777
    0x60e0906030703060506030a020315011d01060e01050a030b1002010606080a1512050106050907171008032d07060b030706020d05030f040303090804060c0b09010221060301141003030311160210 84
    0x341c80c0c238010b8074180402c14802c1c01c1c0101030f203103561502404080b42d800c1c0618120564481200501850741c0007040e016080e9000e19096491307014003881903004080291080750b205032700c114002c040983c1500400150b640759580c0741010740318a01c2c0d40c01540c0d00d0641d00080290400028801031a54a036110b2040340607000224080f13640c5c03004a80240403d4403040c0000740310240e03c0300b00d0b0b04a10303441c03030b045142c02d40441000c528003400720b5164020300086100702a03200c0b680c1d00f0110704801c10202404c00c9851001d50300c64052600c20014995100f1890080c0104d01d00050343c6130020510006c4826162201461a942e00c41040742011000300300704d0074190b039603c8076030204000708054000340000d92a0884920303130604180f090034030020031241d1940c1c0100407545441c001021212100b154a41c0140c41c2911005e000038090103420a00a04103a1004108203029154090320400c4070701a860030041043c81c1a003c03400f602c54007a07240e00c0441a00310100060600503a4201002118 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 102278273 1250 102277023 102277033
    0x3100207170703110c030307030f050a1202040f06030e01020703210603080d0c0206090d020d030c110a05010212070c08030f27010605010f050c21071b060e090603070306050603 77
    0x398912560342c02610707060f00042d0440001c018109401c114400304420308a00a44c20004540e40080c0307640e9040c0b00c011b003000307004240030314820300075442c180880018400a40d12a512041015039502c0b40384960400a4200104400140810b10840d6034894055031100c02600d00031342c0c200414441c0301c4050140503074602c0004082603035080506100c6440800105203044052002882c00386e010b040603001e074004803410f00e801a00010020140c80d500d00700451009090780c000c0e01e00c04074603846400207018990f5100700300b2a065000b01384d20b46075005210032135120004100c561140e0742134010910302c401c001040d06804500c192a61201181c2c600805640c4422155007401e40d80e22842541c42c1e4441405002c03542c0c2240e00000a180c007440d040d800d007441c2070700c2142e850320540c9080b00c240303245d40d00d03207071090b4802801c8902d09504400d24103131290b0602d0800b40382800c14810100000c40050344800030385403a180b46401050001c0c005c0ac455411911030034002c1c20050403240c1d0510603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 102279523 1250 102278273 102278303
    0x311120f1218040b0109031103070e161e02030301142d03010b0105070803060d020d0c030c08010506010503060d0b0606091c1403090904060c020a020901140102160503100207 76
    0x70005005001221801c4648420309103802c00c0200c0090340c00340c0d100e02d0070618001c1d0b0301d0340d0102c011021260440c005460440c40e02d0003003070500e240354004140c541103c400b00700000502e10320045282030300c1d42d41d03c4044400c0242c1500c0c81c42c0300c52500f00050700200010030240b54451515040090024030313100c1c1550317281001102c20f80201e890300220140d20b1440800600d070038420240585401c0c20018074000080e0340d42c1da0607200c005d11080c810040d40d1811015501c8004402804580c4580302c0083d080c0c43e420b02400c5130f421441103102035070030140020890b512030300c1980c0c050307800904203100742c2119554260801e000140440d800510500030503021382c0d184101b00481602c01504400000103a090030120025192048070700c65004208200413600e444411542c4290841d00000303441c41e159900324201070041602a40c080f80b180d0011400582d000002c2c06134060036022a43c0c9483c0000c550521105140305859040c8c21464450307940001c541c00400303080d4070805000c0ca0303c0341c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 102280773 1250 102279523 102279553
    0x90b0c070e010608090c01020f07030f080f04060513060c0803040b0411060f120c03130206030405010912030f0b09010503070b090a0b070c03021305040c0b0d0f0e16050604031112 78
    0x80309900081c0055029000d02540c401c1c20f006c0c08000000a20290144c13103280d001040e0ba0350180c0c4001050340152003080c2042c8a4401d081e5010511200c5d400c541d110f5071184000d02c0c9401511002c0c0d00c0c4030702c4490005286000d203209102a0f40e00140490650b0b4403034468002132507004200345c1c2c114166442c4003486545a50003018403114181090342c0b5400310705046521008010038042074040c0401c1480014103a10800792400d560440740980c2d6a680c0b40b40c440e0142c050164014200e2080b0300c0e0381069941c060304036600800c000c0d82d0030880021035008114003072800b8400c0c3c0e070309500008018022401100010952000050035800103280c0d10350360034100f03a00243d420354440542d003c0074821031800e98071034891110b002c0024452410f141e00d40401c025100c0c81040780314000020000b9052115801c0000c0b26401e00c0410010100c00070f6060f5250780710700303d880b01110b212a50210700ea10703044003664181d0341c208940c2c1100001850502c90040c1c1303010044c000501c41e001c40b041e0101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 102282023 1250 102280773 102280799
    0x309060606051308010204050a1a0d1e05060f130c0e0d08030a0506030703030e2214040b01120305070f0206071203020a02010b040204030203101e151a0a090b0c07 71
    0x10607680c442d030b9a0030b41d00112401c410881d420520490340100410841c0784d4070002c0d207a054440d55103c4041180244107680303658400c2c00c9414040030f0410315162598a09074440e29078650391824144101c1d65110704000560010451940c3e0080d141086003a04141d1603200019032042c6040141900b1341000006403003071814001101c1c105400410814420103a024441d0001300a6009050481c11990041c0c00305103907482c4140a1400003410b404441c090160000e080c50b1201c00420200c01c0d11a10b40c0e0116204840c1a130356190b03074100000d4158658980c1ca5a242d07015641c0c00e0410740140d60b90700c04002429001e80c1d0010050004d10081041801010640a21a1030060b40d03440160006802c2d03039403010f070aa12a502c1440100050f8401241c0159030726502c0c14005040c0e88420074071944c0c451030106070303035000740b03407030704c1c0d219115032080540e4165000c1003640042c1d0700000181445c2445403824040014080350020441d8003589005000140d9001054079080c6450f000540025 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 102283273 1250 102282023 102282029
    0x50306100c061d0f0d0305010e161209050d0905010509010c170403060213090b0306010f0303080702010e030f09130e0712080903030304030e01110726010e0303160801090507080609040303090606 85
    0x21340221500e0700901104010070b1a2507107841c10207004039890a407003881307110b80040c0700d1184200003105162000f4400d000c2c0004000300c1c08070821801400d410815a90181d1850000200e100760b40041500d42c040c506407050340c0b105035071350704200b005039982e80424403030b20b0a8007031094400d20010001039501d0020780324011006440d604414a00013441c0705851440413002d0094000000520914015045410641c0e405003092105070700c40940c00c03030062900c104950840d0002041014940300081d00070079000008442c1e4919242c0041c280800b01e0305120395880040d80509410030050805165219166001315091410248060081390840e40708540403800103045503004041580c00c814018102d0b120740000305041030803c0b0252010701e800c0c0313002d40d944a04840c1d0030b491036202504500081d1068409072030301e030b0610401c0b500d1094044c541c10804a0489000880c8401d11071046510840140e640d500741f41e111340052003a29107000d0410340405840703030350201c00706506000d00001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 102284523 1250 102283273 102283331
    0x80906030c09031b030a020f01170103060518120a0807051e03040606150f0806120109050c120307050a0803060406090203070c060c0903050c0f12060106020a060c050306100c06 77
    0x740b2844102050704001c14001e4041d0140a4a540486151000501108042d034190350681184c02c0316001a500c7c40d03c40d440340a080c405c0100080100100e80c0c00c101d004850300c814034203556000e90002620780c031660a80809039030003848403c44051040b003145400c0041c03401c125103003070f410502c16600c200500e4504000000004240010404031f84103001c018140e0303694410104044250007440304800e01c240908206408000c2102aa02e1004000a100080d4000c00c0503604a240050b142d40e0148501072061f400203900b0030782043c0c08011544080e0b40b14003d080306180c29666407000303800c05407810f5000765881a0202d2034408520042d80114040d4884148401d050320303011090301d4a080040702000700e404010000140c00040d0100d1444085078420860740015020420000380c0c41e5215255101d000000039003680c021841c03d402c2801514140820254000306403603d10040d911590800b0002000d052400d104001501846201d10404203180020072010001c041c1c070a0070f4621 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 102285773 1250 102284523 102284527
    0x60310030210050715050a0221040605130c0b0319091a06061903111909060806150a0305151306050414010605041a190806120127080906030c 62
    0x5600c2c241010045042c060300e005482c1500350b030f85001d03100400034500b03042d0700d8461002c07a00d400c00d41e40644a100c00108a030f4811044100b9041c088514207417415100a172a040206205440b408152100c0d250080344a051076440e004000059900050a140500b0340b081080c01c0492036602038440214082d080c60311307440b51402d906038400000500a10f00c101d10411202142405130300761310803480400e00b0001144440240c100019100300492448502d0000c1d90850f0083c1d0444510400c1c5d4001c1c0d942d66000c2d030355000901c030145440300d90b0152006401d004054030903210743c0200d80d00052011000c4945640700d0040b62050704203a04644a103500c1d0141803149043c90312490307402e800102c640144551500394090b00600c03031402010b440888c1a00c02c1e82c44845040112490802c004241004815180c80028004401a03540a02c00c042182000d60030800c14000c2201d0590b20008020308101c3c0801d2a150500090608507202c1d082441600125035400d00074511464040c0100d503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 102287023 1250 102285773 102285779
    0x1030c03060f0b030c06130506070804060f0201020c0a0f050307020a030b0601030b04090209130206040f1d0a0c0807110f100b0f010c0507050103021303060207051f0e03071709060310 80
    0x21040d50107641110b240507240892410703140d500041c0e4176800110685140380d980000b00c1000c264106250002600041c0c001340480402c0082e00086c4110340540c3d40d03075005607020190407400c0c1c2c4038000703030006a64002c0b0b0818011914aa0134031101521440c1120301c2d204981e40400e4806805134001d0319a403c0d20703420032103556014004c040c0d00d820115000c10050100d43e000811400015002002846000b1401d00c2103450700011540681072100c4100324140d074500302c084642540c02918840080110b003c40d54400041c0a403048440c001d840700c40d01607a030140304035403101002f44158407138890072078a188482c406004040076482c1216000c03804a00450034000000e1600042c941008140d64811003c43e50229050080d66024a4056aa5004d440c0c07444060f103407a4101609a500c0000c0c074404001000a009448041c940d4402042c501084081000c4620000c4a0003c0d1b400c05c01c8000001550300b000111480d81c1203210300e00b005071320300106840703800c11a00001000c40514041c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 102288273 1250 102287023 102287033
    0xb060d1505040b061608030a02070c0902040302030705150d050718030303050412022802010306030605070201090c050f0102030d09060e010608030c12030c0f0a02070302030303070507110a03080910110601030c03 92
    0x1a00c18402c0c0c030aa85041e00310000803612a0703221714050041000400415816652501247c0001d60010b4102c0780d115194000c0c54000d50180c81304920910800384001400d042030700c05200c06a20b0801c500303050060070a10b0b036010700310082001c401c2100c4c5c0501c201e17841d82d4409030880550f005c1e9400090502d403915243d80700410040c02c01013554403030760810b003205d40c0020016405200480d505944100b1074401a0701801d01600010130860505e010825040da0540c00141c205002e4005030f9803060307070f440c02c3c04180842c81c0302c0e142c0160001c129070300b40151079810112101e4402c2400080b900024503d00e401c4a020b508100c0203030b0030020741e070030440804000710050903c9048006103941044215040d562003480301008860b107001c03950070303c0c02d8020301c1588011031300641520b40e00e181030b0a00400303582c04101c003100c0d00000c0580c6000756042c00c2590200341c960104040d840c1c103011301c0c104560f140703442025200300032032050340c041d241d02e060207818002c512078001078501500f94135203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 102289523 1250 102288273 102288281
    0x501140a05030c0a03120e0607061a1504060302070807020a060509120105011203080a0f05090601061103040f0e041b0303020c09090105041a0901110f0d061a0304060b060d150504 78
    0x1c0c0300e40c2c00410750781c04560301c400c0d014080f00e9106c000035900501c9100d040e1103002004d150240d0151010654906100d09608003034980208400300810035504501004065248c81042910b031210070700c820300103240203138003c01d061070040c203846050503200d500084540e29039070444030000744003040c00903050070500c4070001d4503203000009100075810f044103080e1010944501802704600000403a90502440e4010100000124818811460002062a030300c0d1420702c214400143e840e0081c0349401008400c0c4e5050350018004c0d1300390680f6001e41c14400500c043c3c030684500360261440c051242c0019444801940720781c010788584c100340420032040300401000704880ba41030600f0840010403c3e007560004c101c040043c0704070b0f07845800e4800d00404020061644500c03001400312901e8000300302502c0044566001404001d442d22130300b05498000036000c02140310107001243c00544a43c100701a000306c00f42c06036042008401c41c610550300040c410921483c02c1110500c07580c00c0c80d0117 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 102290773 1250 102289523 102289529
    0xf09020901090e19020a141602011101060609091116050a020103110702130e03160b160203090d060917120f07080108032514030d150b040e04020409060501140a 70
    0x8100c0c006240901680580ca100100e1004040745d0010b202981e0780d00400c00051b540f2030410303079075844501c0c10300d000c0c00c3c1c1010480181e02003201404800c40c2e07120140911000d07900c0b1a551801c085140030980406061484505000b085040c0000c021888c02c000c2980f00950280000384407050141c0009011154228079103503c01d4800c100b5403015817102c0d944216040b401000016400213074901d564158042c0b6042100c0401c003003464030080c00100b103041030186074221621040c030140e20100f683e4904c50040707260303042080d034004103002c20800d0788000103460241d1010345548010030071410050748030b1200304200342044000d100c00b259200801c1980a82c3d01d0600721265410300305110750301d0040350440103d002541500b43c100d501c00d074908024440e0b00a0450342c3d69640005066243d810a208111040f843d2112a00c00903030a400714108a410005103545481d007443c1320b140d070f280001001070380c100e603c0300e41c1d0b100043d440e482214000c00e050900039501c1c00d910030402c42c10340300643c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 102292023 1250 102290773 102290789
    0x30915050f040303051305031b0102060a02030103021012090602030705180d051b03011b0f0f18181811040606090506030f1e07020c04050106020f070e070201060f0902090109 76
    0x4005201c540701c040c0100c0341542e03018100309484540320f6011442a0640e034101d5a054051b0080f68980c1c1502c40046030311300d44007602542d0056840c842407000300d000034400a9480416030440048881c01a0388024550340d4040b0003060140c12a2186003d0783d20940320000052800500840c0c2415544030040990204803514002501c05031180c5035180d840a8900b03d603000d110441c00917542e82503003c01d9440c5000c0b00c080054400f0390308082c0c1000d40c0031400350003082e41c44001008440c410a90a2004040440401e002074140b171424454043e40e13598100b041540d80400c81c601c405601260300c6403910442c81d0007031682c02c04080c00150b40c070341d9210b0010305c80710410900c2651b80b1141900c0d4400d19044681942d941ca40410022889000045c450450324032024050403950115410020400030b0360305220345c0e40c0e80e00c0121303911020b003c031400c000e402120080c45650042025650813520318070022806680324100300c220998243c0c000b1101f0b41e800900342040c2d58010360307050f00400d001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 102293273 1250 102292023 102292027
    0xf04020906120c131d0d09050303040e130f140601061101021e0d09020a0306060e100b090409020102120a0201020d050f06030d03090203161d010b0f090f0a03020d03091505 75
    0x180c4a0695140708040030140300312202c2c2d044040d003892a50140110172801184458400341c691401030b20340b54982440c030005095400041000d090005c100e500321504407081c030a01c0c0c1e558110381c01120445071401c40740c91082c000070702c1c04120b03d00c6d2807503800100072024144e00c0d403401c000a40900c00003042c1840300d900503c42e0120311401c50386110314601d01610b000c0d0340c403c50046034000612117010020b5111164603008002d00c880c81c1d0254050312400100c1c10425100c2000d400c507005c03094800e82000e10420004012241055006400c806106004460482c4d0310405245550381128003014010b030360215040c403851206001e0700303810481800380303410036040c10f01c0404d403503080f000352040916407201d80e40b004544003000b00c51602c40c20444860702c82501c607201c42c02c40c040880a15140403c0903800407501411400c01c4985218a108500b071401d00a4014405000c0711b401045a00080c403c8000001d41c4640c030100d40e0480c1f091703450300961703400c0883d5148120140c0e44080108101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 102294523 1250 102293273 102293299
    0x17010602072c090609070e0f01051e0604090b1e03071a0f03070c020102060a0b0916020a0807051507090602030318011d0f010609020315010c050307050102030f04020906 74
    0x22500e50259018000a5040b9030340408082c08404111445a0152039038201000300208003c40c485000340b00d180c0503500e00396500c0700c8159002c8000d69071001d09003101001000070f858201d8140301ca080c0c2c950800c61001107070b00c0000f61150866800502016150310320107a081c90170314209081c55011080094a00d4a01800310350b640320640502c0b41c52180d8968413400c03500c105000d42c1c85800c000c14800d640c174941030100800040943c24200d01501c600390224090300d040b40120368042101808440050380c440c098000c401c940142484258043c04543c0008140148003e00000740100f00900700081c02d07154035606101c00400000401000300c50510031030b43e01000300d9400030130780b04502c1c210500c0540401c2c010902000d441c810080741800380104003001040e01e034801d904c3c180c002c100c0ea9030b6800d07044040c0c0c4001c48101e20f51101e130b0810702d10703d91b00418200c1080e038000e02c1240c1c182219a543c00d800c9034420703141c00540c030305500c0c100021482c0c0103030b036654412416180313a000000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 102295773 1250 102294523 102294527
    0x90b0c1005090714030312010e1017030403030306080f06060402160501050103111f0203030a150e0a0c09050103020901020309060307140f030103050601090e030304060515040f0e010506010e01020d050d060321170106 94
    0xb41801881d00012000d0085000780c5c07a0300d0019000b03080349480329240c801406168933620380c058441140801c2c2050070004000d400800d6071040c00c407812014103a16642c910410000b90701500c50030000270044241d10001c603c091098501841c454904000610700b1035040203880c80c0d41400021801c6c0b5805c0e1316080719507020054036084980000e010626000c0804c4800070001290408000d14540d81c0400050003e42e03000a2032408031900c509038500e032946c004505038882c180003075001d42d004008410450030050011032303005d01589003c62444405d800d003d00594840074003448604800310060003404002e000d6a8010310f40b144e410030040c3c0d1001c00d015102d00005001401841ea20400190302c503114030000d20686c04024001c110442040011500804403507030900599842c01c8001040e95010b0b240600702018160000d102d20140284200d5040d071204207940d090507200c04000000905c85460050b64180e032100754a0144501c000c014401074455440203520500e170750040024039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 102297023 1250 102295773 102295807
    0x1a0604061205060d02060705030909150d1502041703070b091f0b03010b0306090d0e0f01080f0709180e010c080412050705150f0f01060c03090b0c10050907140303 71
    0x2100310300400d00d0f80e2141c000035000c03e8040f0001e5001440020030030100140800105500d98040324110b403103450368200080c0101c2c106e006160850350601e02400840c00c1001400c00c850821a070143c9401c0d00ca030b010049020ba5000c12a03000c0d0b1000c902c5a08014680200a50003180d000003007440e0301c0e40002c1001c0015442c920840d0280c2e03200e003050f0041c0ca003904044c02900d000b0b81141c0150030504551a81d40100b03140c1d810020b50404044c0301a450b24a6010200820503981c11010341c41e44416040a040701030200d4061007529140050411201c0158400312000c040d400110486c50710313401400d40b08605200c5080203c401d0400c40028403552440b00c0502c0c8528003140c880f46c2c0751411034039010f121001340c120070040c2c004025a0742640a82d043c807440300000000303a10b07640d4140969405841d200000c0200d2440c40051104500e4040900151020304040310400454501c41c001221416104091141c000207800e00c00010740da0360b6101c580b04154001e518004008810000e28 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 102298273 1250 102297023 102297047
    0x5040b070203010b090c041a0f09012d0201020706050f100306020a0329030706050c03030601140415110f0c0d12050c070f05010e0108091b04021b011a060406 69
    0x2400420500e056480c01d40c04802804406030040f1349034201440b4a102e5500540b080f00040c500d00e0304104c007a454581f09640d000404410780904040324840103603a082000c013601041c841d00f00c2008803070303540d0f0500d0001c44134040342c00041c0e803101c043c1030100503580001c050108040c03584050100805803d600c1c0b80803203810041c010784848180208030701806450400d041d8071002c001113040d2440b1051404c40c08030303904404640301640c4c0d460040d180ca015400c00040039030070620000d6030395405486007003501003000c1403040c540340d1a00b544078008801d9503050000074035890403c0d04562010444c070000360384514010f056050034400011004241540010720f540d04280500c1c1e00e940c00f41003a1420441d01c0415240207507100c000514508009218040c000340b0f0224000026502499806005204900113002e10380f4441c1c0a02c2e0710204645a010b030059420400e840502c55100450148020000000b04da03030150031480001039501400528072418040004200b0250081c00702c0500c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 102299523 1250 102298273 102298289
    0xe09040f0b09100204030303151a0d0506030a12050c01060b030c041e08011407080f04020f060c100609060806370e0601030f031d01080112020604090e0601080714010504 74
    0x14990b14440800e060001c0514003a46440c00481d01200309074040c1c1160413006414031002c42c80c20b45d41e68803205081100101c1190704102088101104a16500303e41d1344140c0203402c0750101c442c40c2c0e0321900900d035013502010010b6000b041441400900303000e503038014814074980d1825402d081b9a8410359125a02c01c01c0c0414080480b22148209030301c000000602000000300412043c4101403400d00b1011600c0c10000340c0480e0008a0031900c40305000e00403500038107491484d6000d03a0500110b54080011000303a4490003500b103049920038007490f0b0103001d40b09008200b180c40d21411398036160780540120344103c8403402c0a10703a50b1100207a04102c1d000480c0000c500c0307004810711402441b107802c0c45c07502401044008018000b0000d10050f41c58401d0399944140c4080711801c80d07880e012070741c0103400a000300307004002d0408482d40381200503000070500fa19003030350b41059030111000d111036002d40750800c80c0104021202889204000c1040d802d40741454801100020580d204600803054 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 102300773 1250 102299523 102299543
    0x10030903020a0213020703020d030204080d26090f010b030a020d0308040219031101080a0e0706051308062409070c02061c0f05060f0f0303180312030a0203070e09040f 73
    0xd05100700b107507000560b00078118521402100b40303004040c1d40b00100540140c401c2c4112012028400e200704d03022940c81101601043c1d488010803585480b0051642a90004e822540760060104440290051403840000c0402e9009072303000320b095544c3d40c2c0416100f40c01c5002d03503c0c05615224102440540d0600d00442e140e83c8901c0090101540607001001a0580c07a00c080204503400d1710002301032000362036011140ea20304880b4015620100d100001035003003404100880b50144014200c001c101b0344100507a0790b112418036240c8002111044180340400c6500c55002c040c03030f6102d00d659041541c0300d400740d00d403485002d000d070b0403480c8000303018000001d0074814007019005040b004002c000f00501c00c0c1049030064402a003c15141d1030700c51000c2032400c165916000700101c002040180c0914181812202c080e410284482c80d22a054060000c0180c5089040b10042d841089030301c0c00140c8038240104c1c010007060355001054003c010240038440401c0c00b00c1c0aa59420351b01140090f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 102302023 1250 102300773 102300791
    0x109050c0417030c1c0519020330011403060f041e120215100b0d0603170703140306010801050402030a060503010e0c011103040509070c03020c0a0b090f03010504021003 74
    0x9650300c2540d000b550361940959600e100c0c0440031004041c20101c1c5401c43e081d0302c1d4144e264107410700b803d20800010403810444070604208111071030000c076250f401500e0401c1296074851400c92a8022095405000344041d103c84107130b100c00d070501508524070980c8544c00c100c00442d44c1c0d1b44006d01620040b500100004d000c2101d80458920305560340b02030f042040c00c1f1803034044c0311382e145c1425460150080030b242e085ca00c100b00d10305902c501c54240031440500d1030542000526444815030b14503030b43e110074021012615043c1403100c00903180051a40e1590181001400c01d500382c061703058030f00d504000340072650380c3c42207032141502c00031200141d80707441d25400440108126442980c041d402e180039090701440100704010744ea0802c0e2144a01c0901c500640c035240d00c80c1d401000c2d40041d00d400454030b40c034490040c124800d4441d004030b8011442c3e0038006104200185e0180000c3c0000203007040c00d40c20202c0d000d0000c100b0590083c06941400e034001a50007180d100070305e080541d985c00031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 102303273 1250 102302023 102302041
    0x3150501060203121b0d0203011409090d030e0a060603030e03061311090a09020a08010203010617040b07080402121b10050a0801030335090f160504151701090507140108010905 77
    0x541c00c581c5c5218050769400d940060384082d40091207540b041812980c0e00304114102500400c1c8210040f401034840c14134080c1040e4014031395620300070030521030001c00e20b0000d039482c07142d1006103002e5150303c94940d40b040105850110003c10040400e10300e030448030f00081090304401d42d000340490780c2c0603003035640540140c000c01c0c8108000e54080c5180800192600b8194000e5042e140d265481183d40620701800c0b1060f100180c40040112b2103100c0001d490b10312402081e50814070003448000f1812003108000c3c90714440c0f21820aa106504911403000d191500c400580815036042c29401d01a94140140c07082c1414440a003d018030406070034003a00e580e41c0741c008222810b4041c00030501000c03040a1103031004850320f0031288030b0b25105140c15100010201e88803242c18603085d204508080900016040119409a00000e5400007150070355100c5841110210340f140000b4081c500c0c1e003001440d050255111654180f4042e040c001643d9201001e036040d65040c0c000840d42d80c03100086 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 102304523 1250 102303273 102303301
    0x50c0a0803060d240b040b130f021b01051012030e010e01050903030a08060406080303100303030c030b040c120c05030c04090b0607050a0309030c0b030c0306270703060315050106020312 81
    0xf0042089200041c56005000306900c0b01070380401020307040061404880900044410781c82580790701c04030800112034441507507081001020f001c0309025013040e0170181c101161414549c17618a06035118410031004482c403101c08001012811401c0349501280e4078050010f04200b0045810482d50000c1c1c511140d0044081790142d0703c014049a9a990079440c00900c10076040c0e070300502c15801c203080082c070395000000307482c003a00240d045079071881d03c1c650307050700100303282500c1030305060722211244401c0c1d032144100d001c40d00454907004204030803032005100720b4a046100b4030500000f401441700880e00c4000b0350342910100b940018000d08080009140d0340202a030050051040d50495410594031040c4802100d11400782031f40e03040c2d20344a10400500080741c1c00d203442602400011118038002c40e403a5811200b04100c141070b4000604801040c61046845001080d20b9030010010007110643c1c0c2c1d10341c880d80f103004100c20750403c1da00a4580c410103902544c00c101c820003082444482c010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 102305773 1250 102304523 102304549
    0xc150237140409051806090f0f010608070b16020312070b0708010608060f0301020c160602070603020f0a08040f061a0310090203031207050c01020406120b01030c08060405100e040c0f06050c0a080306 87
    0x40346d00358134124005036500d05070110312032400d0180030580120b403081405990261030341e6134040c0040b01e0829003c04003d8120340b041091424140d590382000d602c09210796000c40130303005847c9560b00610b0400c2c07500c6240143c800010045660010422140d21020342c80d0403400071a00d140182801200290280c000c4040610450081600c3d50410f141182d8581040711156001c0e64245503a542e0282c0c2280181d0585484000082090880d400c1c03188444239032082c40703400045018134580d11510201c5590780d140410179030030f41e0a9590980f0301000030210100a500741171084114560101e0340701c0c020b040d0b06181c2480c824010542e400e0052080e02e040c106030388000c54807650b8a400061440d203885160b40540b510b00190b0304010f520034050308084a002d51202d140c80e45035101408010f05000700004501c2406113004622407219029042c041c0c5c0c081d4801405407410484d15207040300695111006120003003148080703081011810703080c01a0000f103080d07140c4c1d40c1d507408509061500301d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 102307023 1250 102305773 102305821
    0x1090602031501020706090609050609120f070f0f050307030b07020f060709091401151110060b07062d0c02150106030903020c0306070c15023714040905 67
    0x310030042c2070030981c1c2c15006180320980c01c030b8100683d902c1d420750355a1a0b5000303401c00612091821300060a08400824039404090f096515422000c845c81d03007003664a00c0e0981080d000104200306e8101c00304c40d0350018000540003031040074900000290344032943c2c070004109901840020344030f5402130000c5900c404410007038400ca071a000314020030119241c00361142091a0256550b100f90040d20210305880b4506808507403841103040507030b030300303541900c40b040c25105042d03a604e41d46000780648401051360030b092603203400301d41c070b020f031306444001149140c14080c0c03418014109000780901d4000801a1000240c2405251812414610007242450310b684e2070704000074219606502c15400240264255094880302c0400c05441d0082a00d0450014028200140118400555030000ea0f40907010040c5031840c1c0d110781070707000703c1c0581c0816150f15441900d400019250f4444442c0c0880034035080d8020f840d02042d0110f140502c1c0655115140e4490025443c40135021111540071045 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 102308273 1250 102307023 102307027
    0xf080a1404080325210905072303060408091c0501060608040308100605030117101d06070203031902030c0c010f0b01020d080603030301060e1f0903020901050f100e0301090602 77
    0x260402c500a42d006540030820003500500e00c29103038041003a22941c008165580c0b05071410080b2419030700840400310141800d03030700d070b504500095041003004000e0658a0b004008081d966070750000e820312220109001e80c000701d080000045103501110b0070043d0895074050030810341079200700c9240301e030f040080840d0320300000400d090342c114615511441c4255103c1c4083d64030b203441d46174072000600ca8440441d41c02e2006120f0014820b10800c0c80c507040d5003c40300d010007084007040a581d041d03420500a00014517907120070440601c800c59008980d400250710354188032408030540340350001006251580400070030103620381c41080320131601c681402401140a0b51002d4402420413841d82809445401001c4c2c491034000d2120a01c1180c005024600350780c41c0400a5400c1c401d04a106c0368000c5000e9800c040c60120f40d248803440802d42da40d0080c8507815803050151510068000c01c3c0303c1d10110142d8601c0c1d9031004090a0141e1007840c1440300305101030082405080c074050000c2109d400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 102309523 1250 102308273 102308281
    0xc0501030213030b150406090902010c060209120a0b0402010f14040504090602161407120206270a0e16050306060702011206050a0902120105011106040f08071203150906060f080a14 79
    0xd45d4840f43c01880c0100c41c100581a52842c52904a6000000007400b14102c24030030f0740810642c4e0f000c1c0c030500a000d0b06881c1c1c4501c4c0e02c7e10700703800d008003004211520b14600c030902c001e41d6840744440400059504044612854081c4c001280780914400c0500c0341c1e4a0350400380c02c00001d40c0603104100c0800215946001244c070703006031a250b072412941701c0e80c401d00c04002030700c142c0602070382d01031500580800e24008480d10340c00e0800d003108004154131300b010101c4c0021a01c48d494007070f0003404041c1c080405800e140b90722034003950800d40468108481072090190503030f211801c845500390309080c280b96040e00060304c04041d1505500c00c50340011b0740580000d118405400818034021508640903850b0303241c000640340c0700b1468441503929444a000130340003c0952081111791801400c00d1400c00d42c0315511001c0d5160701d08201d5000a4503201401101c21203498240c020b0f02000500307100c25030400c0401040054500440d608110008010403030300d154551020010b222480001e0100d80380c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 102310773 1250 102309523 102309541
    0x20303070812060f010318020f060f0301030305070309050126070210020c0d0801120309030f080d050c0d05060d0b070302090103060503011404030f0c05070302220f1b0c0c0501030213030b 82
    0x21040f10300030f01942e90403c6070a0300b9803192085414401021204503c0510310b5000d0182000d15403040342e81080b0100700350600c04c1c4c0d40c2800341d0700a44c406e5031401e503121035520300100100300940c002c07410700048003010002030180201e6540198001c24002e0043d9903a200100d18080b00c00903040322880c4001481141c41c00c002c2180725601041c1d0722840c40c603980e100450b540e08070748140040c0014142c1203041c40020000d5218001071409040b103141004180320600c1c0440b1419503032214603400015142000b10b226000c0e16601000481e00d8402081040e19003100101009001404060380002c1030b40150380250b0122004c0c080c080d000300164002c00c5c1002c0144603090390290082007480d0040e080c03040c450041351003a2a4090080e00b01e1924650a00c401c214904a80240004011690001007401849107018200e900761000c40c1d81c4000e140f0b1411401c60300386054003003109440c030100101d542903090804541080ca030050740c400980500420300e1210390401810480c00c4000d1100e182 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 102312023 1250 102310773 102310807
    0x30304021c021216080708030a0f12060e04060b030f12091215010311090709153e0c06030103020906150a0201020a030b0402090d030c021c08040306050702010b0117040203030708 78
    0x115041080c051001c5e1503901d050b035200b00b03038401c0f00800d510801a4400841c85000001455003040c10000800d40320307580b008040c0c51032500050207584100e0200020300a842c0211488a081030300503052240280392002e86401c80e0005030741c406200010f6092194440b050018030b01d104501c01c1c0c0d44001e4489000040f2310a082c8001e0fa00c403101c4c11070950076864809281801890b0036141d610502d031908184090b4003600003105818002c420b0728546810b00607506204001a0318400740c01004141c0d29400d80c2000074050381b210950014042c00c5980e00c80c0340072603043d242c0444d120a110340e919000200005610410f81c03101a00100d44205400d805401400c100b01142e1424445ca685a405110481c0a942a160360120f02e030b40b45100442c0c082c2544103103141c0094202c90a046000c01107042c900300d00c890848070b82c40300103410000d0220501c69203400c001c0c544020301540c440040001e10044d154818070b0548500f01c808541155070030012101c0b559030044e07004d61620071125080c01c40c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 102313273 1250 102312023 102312043
    0x181401030f0321180219060918020d02030106120c091206050a09080705030a09050102061303030f1d0f070504020309071a070209100e070201060b1603120e01020a090806040302030304021c0212 84
    0xf250340000c2000c0e010001b1803207800f03a503056601c0c0340b0117a00d03080307020b10501d0005000d044100e50800c07010004445600081d806030203582c8642c800340d0382528003402103580ca0701341c0c0ba0400040190910580740c00c0b095050710141c05c800086025105e0000c000000c00c0010070081003510002842800c010001c0041c0c02c1e03d210a0700d40001d5603903103030010780e2602c804440d10109010f035240c080300040d00943c8140c0700e074841500005255403196240c200380d1400c0c683c1160050b80402c10000140c841002240701520060f070341903046050140302c0581c1d440c01d40c000c0e0200268440280c0d01e11200c15000d5508080e0000d241015078200240340001941107806003458444604000500e028014019034044070b03600b0300d15500e4640c03042000300848410483c101d0030408a501a2182112640203c82d0a41400c00c00140d0302c08441001401c03d103000d038030030a0550013440800003c242c000c41980c0d8820b130107840454a68141012414a0786010b510081d0720a211004d04580440300241c90224 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 102314523 1250 102313273 102313279
    0x20705030c0a1a01081207030c1103070608090106051504050f1810150507030e04050711070801270c030b070c0206130602190c14010504030c181401030f03211802 71
    0xc140d0303c61143d1511b440c00002588a00b004c104801c000280c8603844145400380900b0101c0810314140c40000d041000b00d0740000005074503103040c06080c12080c400e40c0014101190400d88440a81d01040064041c07445164455440c4030b0000c0101e48465008001000c14085600d07107510b4840403903400d0140b41c0c028444840c0c1c0030100c00d040d00e07000300201c071001030b05038643d0b9040950640400010345001029201040184100058060310412040c07002e42100d00000c50485081c0d0000c800c070004990f004030128a80121040124070400c00f94800d40f500800b0790343c80e968039140c0540d885240c0705e01c020340207000020b80313143c0600114050340c01d54a0507030039a6020300e200e83c20300d40791260410015001c070403440e0b001c00c1501804403c244880350181041c0303080c641d4949940854040d190310120302912080ca80c100c240085218152203006000104a202d50654485c5c00c00440400744c01400c0c00000f800755248402e00c0a805070121030b038a03a00313000103901d03020700c6030603400540c8040380 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 102315773 1250 102314523 102314573
    0x2f2b0c080f06090402090c0c011e0e070612050702010207020604080f0d030605220b031507080c04030b07050c100203091501080c03060f04111008071101140109020705030c0a 76
    0x30110218141450007520003d010054a407525020000102e10203800c1903a825000c225500d1030030300a004000074000a68194101e40c044903024109640341c02d50a80d40b580c006010a000c4980c11010291800c00124400501075a40700b00603402849071000282d4440c41c0840c0008203034000007480e0900796100713400e0b0303541c600c442a0103034140d850b02e0140541c0002c0043d00309590002904c1c000c0038182c00118003086200803200441e08203035001ca49583e20004200030000d2154100c8009500120a00d010034542480c40c2c903464001d850203003050081203000074184100b034400704213070640881207030b00c215035a081159940b40e4a190b04185140c0000321900001038020021407441c803c900045c02611031a92841446441810010000c0b1003c0f0260b19002c042034a907140b030070414400580307420045080081000c0c014052070b0016408981c142490240c82581002c00e860455818090258840c0c88a18040d811030185007602e4002d0702c04d0410380780c18492000c103c009850108840c2d61 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 102317023 1250 102315773 102315781
    0x120705010b03010603050c040e1510060f0509060403030c05151504110408070902090111030c010c17060d02061608030c0316050a08070503060a1511012f2b0c08 70
    0x5420707213900d44801750140c1c116401845850801d50000c86640320080255518012405c188ad4210308054070490140d490145050012a40003a01412004d60b80c0c10400d0030100303002c0005400e48a1400010708000071201c0e402c0404c00e0411008880b280764819940e114641100301100b4241c12903485403041d428021020072007900d4800322416540c8200140c4002402c200c0a480a5446080d070b0a042203005241c11001d00001d0010305400c212000c00481d4034000051300130103080141c6030070700021038a082401000d650745840070400e5541a10348603110740b0345910081010440e404081c01c0c80d5000020004185d0755200150320072041e800a0903000901c160003114a030007210021004100e000010407007050281014540c0721b80b004140ca0f1859444410086442280890f090003044101307116006140c02806070144c3c011070540d0925000701034419400c0310048608404014140001c0d8620400090000c03c10702c030542c00d18603448480c04111102d004240354412000080c1c074800102d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 102318273 1250 102317023 102317029
    0x90a0902040518060109021b030a02010e0105010501110604150e07060309020307060206040803011a0f07060c1d0a0b13080106150906080709090c1e051b0d1710030203120705010b 78
    0x10740d43c403610410040c0b580f03a0030110b0400c002d6001ca071426419056107041315040e4031042009164290b5560300205148880f6081582583d0060700b019050164503019006440f50000c3d10039407080d0410003104c0030300c04008624000f402944c00d00d18a9000d1894080b82c0310350103402014005200b5002c640c10309aa9800807601c964007030b540107201c41c2e801c00041080c2040c0c1022000b080400782240c074a40920119140820f602c0100103d60b0b45ea11880c2400c0381982003804607203d1019800a4001540f000d800940342e5400d9000b04c4071584804190007243d01d901100c5600a04417100003002060740320b040c9180c28141e00d0701c850700020007100011501500c1a4003070b902440b15500c511100c1810440610080c0455a449400b00202800c144003141d583c0640002c684526031195551100450034120750900f6a02985070564032615128902541c070200c0701c869210f4501e074078005038a69040483e01c5080b180e0010b1f506101d091000e80041071564020a1201d20035402044102059418 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 102319523 1250 102318273 102318301
    0x920070503071b090218010e0301140115030b0409050304051c020901150507060c050c0f010902030a060506130e100b0409030e01050a090e0a02040614072f090a09020405 74
    0x1001a0018041c4800240f64550400b2211078001403403180d054a40070520100d820200c80043e1180000040c6000b95810409802442000340d00901c401d0300d50f0004076030201c0c0107104000c0e01d00070312248648040d219a01101082d44002c00503c000c02050500d25640c2d0054003d0500c991030004c84021807036001c08503084426405001d0f98200e80ca4001c1d1401c4074082c2c80e9514062000801c60400010341c039200700ca10101a544410b070300c3e4004022900e00d442011842d40355180e150004103400759500140751410598481800704840d6034900100e0b1804416030300201c02c0b1410240042000800442d400c1440461035408201c3c0440034002c000c01d40712004400b0b0045401c0300034216603544550000d24022503907050034584955101c2241d00038200881d00c265015502040034001c4581c002d145841403200140303094140812a146c2e801d00500540074800602414124060f858240418001510200134260081413030450100c2000e0103000d042203104915160004440040e40e0300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 102320773 1250 102319523 102319537
    0xd0902090c030f0708041e0506090601050102070f12030908070b0307030b180601030e01020427051806010b0c1f05040c0906060f03020c1903020f15060f010c0f0c0920 73
    0x601c50f042c0c039212020361303e01002400070744581d03004c0702c0512506640c00c40012180c0c0c2c03003000100381c1c909d0000e000d04d00744041070700030f54110340200c0e0081000b510104a40c01c1036a42c1d46c4400c0d000d992035441c0c140c0d040034456000348071038001c90b4000110b00010341c000d9441200e00b6241400b1a0701c4c0c260400032407041500860714000402c901084927944a680f00140d2201881c0c00149400e8807124003610f003101c0003a040c1e940b21090130700b001c010405070141d00e402504240600500c143d49540c616200c100500589501c00800300780014001010072052801e02031801007c05801c148074881009082d040758103840150b8507403000a00d00000d0700c2908111061944d80840807003c2c500110701940c4a040c24421500c0340d408200081c07544179442c2e5001504c00e800410740d074050300b0000c40c241441940802e407051003079000c00c0105d032601000341041c0740d024a000031a40b07a5626001408581c1104c1c003904003c01c0480c04106400c0543c070201d0b01240008545800070009282c65031240f1800c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 102322023 1250 102320773 102320791
    0x607031a01080412030e010e010e1005060307030b130c09060305010c02070510030b0d0507080c120c0f040509100501030804050a05040908120405070e040c060801060503100611030f0d0902090c03 85
    0x100060f02280b03800c1400b54807442d06280c00b040c03081c42d9100f9070f403e5602501c032407c660707591142c42c051601020401650500503815090101d07180c2040000d4a07800c1d1848090402a003840c001480301d486960b000c002503034021880400c21707890300c8424000b00420b01013141c1035840c00c60112805030000800300104d40c03000b081701e5481c0300072180440c0500a52101a0b800c888081070120006001384040310180443c3d00080c56848000001c001c4c800991484800d02038000d4041ca591544940701d0703000312494103440100755a2203642100707107440380b460100c4202d0341c039102c0088100007035500103200700e0703504903021a401c0d80c03038000304001c955149800410140040103095011a03081c44101e901901a0080d10004c40d5514034a0010050444c0c00b2140c10115000500245070000116400740480740760950551506032505a07070b0a555004800c01d101c50b80001d00f00711081002114020428070200c50f8803090740c83c681d900071700702c100c200328030802c111400902c240a241c0c0903644201004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 102323273 1250 102322023 102322037
    0x1d120c01030c020f0303090c091b12180f06040201030c050405010206060f150711041118010327030801030512070503270616021203031302012006090607031a01 70
    0x500064000b4105165030405600403501410b000103001d1014510a010300000740407804010020084846d400410100c5c04031000314031f401c50407006ea001d4a40c0041e2041c882d096640300c000201034290046400c00756103101e142801c0d2070350500800d106018900c01e172000c0c0700480180c10161554081d90140b94016444a800160395283c1401d410340c60321030141461029602171780f0b040090754031000c402c0d0b51092540412403010305081c400e440b81404100c04040c02c10f40918a0358821150200a140c10152030345080c134204000c2a200e41c0d40c00b2546900c00603191601c2c0f8001c0c150083c00d10043e07a00d401502e10604a500d0010304803543c06602c04041c41c60003662081c40380c3c00220948000c43c0c01c2d213410110007005d4450300000c041ca25560164542086402d10401c840c040c5036024401c8241c005000703110001c40d45021a402150342400d21002ca00c03d0854079802c0a801c180b0b00d07402c144075170802c0c0080b81c4004511540681c0c10790b501800101e0304600c0700031189040c404014001554 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 102324523 1250 102323273 102323293
    0xa02011209121d0a030b0403050319020c0f01050105031c08040c05030105070509120706050d02090d06052a0405090a180f030908150603030304030c031205071d12 71
    0x440d64544948500c0ca4000045100c040d460300702c4214610344104021030b8406000b09400100c00000416410040316002c1c006402c1d0b0761440301e2010085c1008082c03080110100c6c042c4200c219200b1002c501c507100c11920b9646800d109580d03142402040d100651a160000c00c46060101e040c01d030029001c818481840c0b4101c908071089040100142e0341404820000306050741c3c2030003624098002e13a66081e071600301000030080a0151050b45001c10b17406000c007007100d25001300c00e072004c4500303110005880c1c01c8410301241002d041c4501c01003070a4900340400044401c1440c840004407c846940c900c030000902100c8110702ca140142a40429030038002801703c2e529411a007000300b0010402a90088a640c0b0f5110820308403404030080354001100b4030002408000031903642d5003c2c4469036032401c008010984a200141028041010b009002c8042c1405403140c00c888064040007000185808000104070203403240d14003070741402102c0503804500e004940300b124200000080c0c403050030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 102325773 1250 102324523 102324527
    0x801020405100c020607050f030406081609060f0c02090a0212060d15020702040b190e100501050d09080702060d0c120207080a030c110109030801180903020706051e0403080a0212030105030a0201 85
    0x3404042c200d0780003034108043c10001f0405e000420714209602e00844e211820b09201411100b0001c0640f00b11410035215154241d511252600c111041c5003001c03001d840044404540c000380c1c5c114081d4004400e20180505903020781c0c004c00d428410a52408070179120401080051241c500020301082640103031054003e2480d40182201d80c4020000521003520002246100b8240c41c3d400d5111504404204161501507040070f902880801744c059003541407100107410390103030300306c0501d61581d12103160003000840e0049036500b640062680303407200e0030308040702d0180c064814480c00240081011081809441c000c4c4c0390803a0b8400003940c2403860810040700100040071180d0200103909801107840e150078420110818080e50318084298100608030307008100b903244160380703289030451010200794042102401d407180c034505a944e45690064404015500c40908800300200142c0002000343d80743c0146444a11074098071006640e00b15a13400c4d0340400d21072160140c10820305900158 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 102327023 1250 102325773 102325787
    0x1d0624030411031603050c04060906051311040b0f0a030606030203010302091609050603190501050a030c1512060b0301050f04060305031c020c01020c070501021002030c0d090311010e0102090406080102040510 91
    0x20005011606101a06001e15201c0103482d40145d406030000b5087c0c810a003018090080a015850780901055142c800441c00035070805803615a180d0745ca6113245000701c401300840f8003d10b10340e1032325600c0c0c0c000c410840315598448aa9903010910b030410024001c0d0280c000c2d28100d0390000c0c402e0245544400c041d07402c9032803c03001d030400c200707a17454080380d140c1d03450000c0c5011b14941060441e400c01000b103c4402c556060704128450251107108100288406046500742e42d42e202802101283d80b43d0305642180d041b410303903032000781028800300b1410302d19000b541c12150115803112500c500350090000300d40140c080030740740360010040c001a0030381002d0041a0010002401481c0c500080c40c05c5003242c0004032003411a8110703e03001c100c03640e030410203105e00c9074507201e045280d4246400c0c0b001441c4079224000040945990b0807405050003014041c10340201c0000034001350300c402c2c030746d103000f03500c1140c903e40300354a0315038003141c0e42405100f51000e542c0c000d40310041d0011014026a241 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 102328273 1250 102327023 102327053
    0x61b021302090d0305030a0b120a030c020111030708030a060b1c0c120204030501090b0601050307120b0d020d03080703050903070b01092d020c1b09070f02071d06240304 74
    0x18030780030030030b400090300e903603c1c2000641d00030b6407221303220b0a20030010005c1d141802030680c031a41841c02c407a54044404140600d45c9039044c180001c0302d0441e480180c0b400d58010a03404564000407a00c5801d01100c100290310070403035081c1c00c029a68030394000d5090360040b900f0b0070100115400fa11154440c4a0344840050200d03420000001030b000e524180590344a50030803120b40c0d469240a9080005000f40d07581c001c002400e01030300754949800010400c041c2c82c03421309042d03500c07020400311075140d440480c642130b5000b604403095450740c0c1c10058010301d82030b00c41100091501002805040f8003100351030032a07500881050261b480c0040c0b417000341c40468843c1b0030807031100940c4920210384008006200484100250b240c592204401d07003064980c82c402c045400ca14140c2c0d50465840b4207105601c41d170681414000058410001c030310f48465604400c601110100b0b040300b03c50000100305120b11011600ba02eaa042c080020710440c050b809644d1030040d2081c0007043c0001e4179002c0325021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 102329523 1250 102328273 102328309
    0x20d0f020f0106141206040807080711040c0818071d060406150f0f0507020d0f150e1506030d08010e0705090303031501030f05061003020708041a03060109061b02 71
    0x4940040c020760840d0b00760f40c00191904140f40440380b881c00d02c440c1d414a981541d6001c0d08071890941c6455407244104000204109000030b510340403c1000303200d02d031680a01410400c013400303009102518001e402c0c1c0344400210700110031112507030b100080303010030b69124a4a2103904010341d603805001c2040904802e6000c0d8880c03c0100700c1040d0704070380c869120030550703844a01e50408040900500e02000340407042040070010000547c4803540b084e01116840559801d02e01154140112204103402c5481802c50404000810003500002d002580061400f5030221301d071a070008041d0380300300e03a01e540008a60401e004100f071900b500c4980d0760004c103c0c01c00c00d20300110100000d0940d0300454001c0d1242c240e0984010803542c0c144900002100060f030308002905203100029500740d10910799a007015000030f03071841000380007000d440c01414441c401407400800b900250300550800c0b10854001840a48005070f405e05c154000d50740381520039005a03050b2003070740034050725002b03258528130 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 102330773 1250 102329523 102329533
    0x6090c01021b0d1713060206060f06030403050706060306050a0b0d0510051807090213090b030601030809150c0c010f05030420121e011803090b0309011103010305030705010506010f020d0f02 83
    0x3140101c0703801c1d00000940213460781c3d5103000360068801c1c1029600f148086612a40400910b0b80b60198580a000c8088410f50b0320307940c3d2498110750500c80c80d003000340507c0c18440c0000070040d203034014600600d1400310a12000e01101c040c440e20040022002e8650b60104074000700074400c941c040c64100710701c1c0359100745148440b100e4514004180d030040000036400500e80710031548105d028070103480d4640b010b010b105003200000750307100818000036268002c0000e0f02c502507941c00c00c1401c2c0000c020302000d40c5404401d41483d13264011010440d0100e59a180300381d01e000e2140d4101c1c0c0c840d96008100c2814440c264800c2e81e0380044603e001900486460000301e0007440401c290074181c3d19075100c118061b02c58110740350035a28a01c0d280b01c2201c65a91420000030f401c9440001030b184892207c86e141da0741c0100d0b00303001d001070100307100c0e80010001c0007006011010005004041c0a14024803d54031107000440f855002e0700c030700703400603004600d9030150180700d0403102c24090399a00c121a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 102332023 1250 102330773 102330799
    0x1e040f050a120513060801050d03110f16050f060c0703030e01030b0409230d0906080903040f1e05030303010f0905090f060c0703120506010801170114010609030506090c01021b 77
    0x101d20b020550503900c0860f80214090080302c0300d001841029007800c4c0b9080d141075140401141494004d06d1009080c405400008a5555410440e603504074000404a4924482d0140b400701c41d0603050042600608401c1d52000507802d00804031010306030f00c90000c240191454604444903241070091904040d11001d5040e2a40d0344c0307004400450740540855140101c810a11841854094101d0740aa4105020140c0c10603003012494040724014200400203a4a02c4002c608510494205202e18100b010000c548800143e20800c42518100ca00c1803806485204040c0e0f01d010921034100d0039403804200341b00745941e036006141c01c003e0100448030120008501c140c20301500315503500d5161008030f25001419804410000c1400104804000c14103142c40028004d4605010320882c01070030742803c058904095200d071100009840424000c0d50311410001c100c2c024520059446100f04000318820680120703d0041160050300180b241c0c48030f88000641c01c140c01001c03140e01404005400c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 102333273 1250 102332023 102332033
    0x908040f05010f03050f180f030301150f09210f140303241809071508161d01030b04060b040b1908070516240906051e040f050a 56
    0x5400546885580c0c81103040c01c000c001040110340000c0c2c2010103080000740040c0c00000e00001750480031a60703070f000f41344110b080303c546040c8401d11007512501c400400054a260804050f10203100c45a40c3c1c0401c001c007090f0122008129401810001600b210308550103018902d0140341c824401e0304c40342c8200b00c45441d110000c8100d5852402e2a41001003003081840c02044d8466007680040c8d511054510940c000c102a0f5112501d242c8050310a2800300300c003440c1c04c00c026801004001e101000a10b9182e0004000c00c6043c2c07091658402d5000f101e005d03250007145010616803d880c01801c6a02c00c080045000c0d104403007849811036599600410414031500040c00a0b0980e81d2100d599542550300c803007000003131049444c0402c28240144007500781e1181c1100d260301c4c404200c4100101007030030711000787e0441d0401280c0b00b0301c4000c03010400c1040c40d08102e00f924001c14007008aa82d070100d12400010310503001c1070740341c0c00c07030b5000800040e2178840d5000344c24010707001c407a82d45c034450355030f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 102334523 1250 102333273 102333277
    0x50c0d0e0a0506070f0303050c0403050a0803090a050a030c020f04050103050c0f0111161d1003031d09040b061e030a0f060b0301050408120108011e0f0e0d03020a11070f0e0405010908 80
    0x10a4036100403030945e000525405009542c0c1150032800d0301440c10b40740d074640716101c103418140100303c2400040880c1f02c010007003000036801034000040d242001c00c00d1401814501189030220300030301140440c04154600741c8180350481e50070202915005111604010240d20f000c0c8029060080421181e407009400f0040e0428810118052003c06801d01c1d0540600955501d03105841040c1030042120510080528808803549810404201940008484480842c80072407a0300011040100003e004040c80e04500807401900c2c000c0c150000704184079041e1005441c0ca5405520900c903200025072111480d000f070a000d80000150740d030420b0006801c1d0b42041d01c040d00d0188021403e8494aa2815065030041440310020007906082c01100080040c6041440c6a9240d9a0b00c00c9000f42d0003e8019902c00341442e0705a402e40c100c2014003900039040071049600041c010f180d0317014007580000d85482611025101d1503041481d04ca24241c1442c070061041b80c895490f10760480004180d040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 102335773 1250 102334523 102334537
    0x60d231b04090c1e2f0705060307050403050303070c0303050601020c01020c01050d0219090302011115010302131b08150f0901030204020c070801090f060b0301092607170a080601050c0d0e0a0506 85
    0x180b0300303403000c031080700e003440c5d4440c4030081c0c8102407922100c00c8104000080e0f008100c4105495040e165500c0039410b0318240941c0d840681940000820812495404280c03500d07418441d0304c4c1000961140b00049a0310f650070b108450160b40070103190a080d601a0000d06500f003031030360303000d868000360004605220300c2c01c0b0380c940c1c042509c402d820b208541e00200780340d100145180041c0340b40311000ba000a00400103100203409900e08a141d00034488e403d401c4101440c0b1801c48100d09501d90040040c21a00d080b10030b400440000d07080501940742100c01452800b000a18a402d16404c5400b000003d510943d0520410b101e1060001203a1a00f0700403240010b002c2e0028008200d0035040880a40d81d507003520301d02c03036490508040001050101c0060302254215500c908220700138540340f08900c100c3c070f4090402d5a02e0b00c0c005c0c68809181c0c004190310740f01b0340d03649040c40d161100196070368042c0d04100201604004104040c0d03600c943c111803202c8000801e0350700003580d15008289a80c2c8446 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 102337023 1250 102335773 102335777
    0x4170c07030c0501020d020615090a0207060509070e090304030f0b070504120506010e07030608100b060c070905090c0409080706050a0b10050d050601080108070311060d231b04090c1e 80
    0x800b00420361701071240020040c041e0000d44018503080d2520744c8801e180b980c40a10526140c0302040600503580d0549040d260700ca08100302c0760400302c40169481c089031003460b000151040004450701c2010090701d007101e0740300051842e004001e41d248096141c0040240c01086014440041c10708030111a6040b1503002d01c021306195410074010300081da0b0001e240f4818035081080800c000701c4002100c50060403070120000c0c1d0b0140040015a2a1007084083e440074406c403000450f00e16103640c8100e001da403d04e0112000340e40c0c40c80904c420380b9000000540310b1401805040049901034003c20743c880c521040c0040d8103611080060700c101c54003505a40010408105245179031058800d0980040c02402c24529a614210742c581e501d04a82c007004204034007100b005400703515040c080d00c0c0c0d0018210000e00c00f001842600d50075881014112424605015004c00c0070f03032060407051040d562035003604920345820500424050203e00201404008600811708546004c889111441e503a4036 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 102338129 1106 102337023 102337043
    0x108060d06110f04260309061c06030b0402091311061317010902091b04141f0206060406060207051e01020715021c0c020904170c0703 59
    0x2da040700c0300458041050032040d0b00c0c440140041c1e401c45501c0e51a0000e00f22080e201c81064110b50614580081080d0100d40c00c20700000e10581c100400025186071468041e002104e80d2540141c0708110100709102c210f282c814210307a04a62411200f4240344410b40714810550b0540804602c151000601015000c0708a080c80000f007a0550000174180752903c0c940b40030b442c0b1810128032401816000a1800e49441c040c00528040e001c0b242d8280b40c20300046c04140744260800c1c9501c48403c1295203926400301e031008511400360350140549080c0441484240c48003074020a0940d0000401488151141e5040f0951259951030300f0b6001c03501600140d0410181da0030403c60f0340c0380b00e0044d0020540000e0041d10046150780c0862225902e00800c0f1000402044003e41c029a02e1000c03a001c46c210414520f803440d40701c140640350503080040030703140402030360084510140b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 102158273 102338129 := by
  have h0 := BRFrame.cov_init 102158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 102158273 ≤ n) (h2 : n < 102338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
