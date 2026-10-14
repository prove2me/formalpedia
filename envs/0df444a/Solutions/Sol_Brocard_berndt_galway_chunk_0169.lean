-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0169
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:14:05.072201+00:00
-- url     : https://prove2.me/submissions/ffb03a3b-80ec-4d34-b21c-41fcaf799382

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 30215832 ≤ n < 30395689 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 30217082 1250 30215832 30215869
    0x402090901050412141c020301051201090c032306040305091e01020a020103050c0d0213080105060d08041a09060304060606030c09080a080903070b040303030203070e01080112060c120f0506 83
    0x1e460142c03107240c0840e08000c4e420f802c00010311800d60b01020494291b490007a0104541c010b1031410f03c0d6004081d40003030080501c24121140701c0855030105200e040c2c0d240e64031900b540306e014610f4680013002c0394064014007280704844511000d038241401480d100d944a0b85416407210100c00c144030a850581040d5540ba07080c2c1c01082070307280c0e00050303541c004580c240380220789030340c07070300800000f6000e0a5052030001b800419084040300d140c1c2040001e80b14880020400c507640c46040201800b81d007134000e0702008082005010704c9003c82d10000c07a814079901454a440348000114a640d4002c59080d90090303902d0000340000b552500841c00241403d1500c80724940c280840b050f1900a80340d4020240c1c480014662541e407002e0200c100249545041c0c1601c495480c18090003a50048901800180c00a05a5143c66016501c403034140e131101200840d102c0007a6490364000e01c80300c4034400520400d00e090034881c98450048003444180124080340905041091154a54003404030700807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 30218332 1250 30217082 30217091
    0x60303080a06050306150604121a0c12010308070303020708040e041401020a0f0513050a0612050606032215060801140a0b0603040b15030703060b010e0d0503090103110408010f050402090901 83
    0x140d030780000d992030b017240b1506103210344001b0160010340188129444202417000702c10b03210b000c0c08007981d803040314680a0842c0030300c40e80c1c1d604002d40c014030400c0c00d8000321004220050012031000340c050198140701e4140180b03416656110a4140d4000f0703032005181d12222001c0008011020301c400c2201e81300380009505105900300d010b0a01d80060445504021011a00d020100d4042c58050000e00000d00703000c0c030480e16510014001d44c8502c11b0420681d08100c08200541052411a0310030480c0c61501d00d03850b1100c00f41d596810840c01e805071003520041c285580da990062059800030200c0380300014600075241c0c4148101480104085869807814404000301e8440604403a070050307103c160f8030196aa09404040385c081d840311807a070035210b103c0d0040104103047d40581800a001d0301c40c0700012034983c0c1004142c0c4c00e02180200355400c28403146009500a42006901103030356981d26040540f9082c4440c01c44120b00d01e041c04423522041844190700740264456080b038074400c020300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 30219582 1250 30218332 30218339
    0xc09030c0108010e010909020a0515090102190203070e09010b040c0e030c0102070b16021c0501020301050a0503210f040b1303110111030a0c02180403020d02060106230a0201140a060303080a06 84
    0xe800c4c4005100300b00c2c0b4143c4a041035011950b940780c0503030140100030800c81704d10000d403403181469013052074030300d0152103000000340c2d1280c04803e60f034104e10f50090003041402d051120ba8050000080c02c0d0886641d00c1e01030b6446566202d00406004811550f2944a500c80440402d85824031020742d8a0542d080540c0921040000c4402c607400c48120015003074840b251440401c240746040d2000c01c114552582c0701804200043d002181202d900300c8210316165122000c054032645130201c540345102d10f6056600f10850b488003d40b1400f80c0e0442c8041c00c0c59516110408154010388417048000d0f8291401d2040014030a0000c100340760030300e40b0704010403540c01120b64074030465020703030103019880e041c4204540d2075a039900740c0f030003051039201140d04091070080d5a660440c3c0d00035015009030000411903a110f01c8450385461000c00352020122500000707203550b80d114520f1281103548171010a200c0381278961402e4040e181c00000020700a155080081a1017070140c04a800d05042c5007042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 30220832 1250 30219582 30219599
    0x1080c0a140906120403051801030c02150a2301030b070e10050d090819021b06120408040905040506010906150c02041d06070f021002040303020703030c15050c09030c010801 76
    0x400c41200712030100d0740d03031080e000c00511180141c851822202e00c3c54001c1008040d40030020b003007101144070020004682c1c1034015410351380c9041d80c6400580c0f01c0520a04040f0310310300d500c0e4000d41200b4001540303010040c028055200c543c005490320740f007004010010031040040650b8000214901403401d08140000a82d100085031505020001c000c40c8503690010958801480340e60320511880c2d4030f41c42640311a50345042e04044001601455420350140345540d2880700c4040c0d40103203032a143c0200c00024206c04500580300b80c0340030009100224010007030b0310a49000354000c00050002c0d6151a01d60760076520b40d07400030450310f04034010700403189070420804008994116070200351840440d0f19101540b81107038854019106007010b100036244c1090040c0c55668080c0d0a4a00146003c0200000d0344564400200140d20040040010a106828940e01140300310b11018448140c40a200c0503144103403800d0300421000182e886240ca000c001000c014032003801d20a0310b81d890130000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 30222082 1250 30220832 30220847
    0x20a08010b22020c01150503060609010501051605031c090c0b07020a0312050702041104060f0c02030304030303051f0923040b060f011101020c03070308010806010e040f0201120e0a0201080c0a 84
    0x1084205000b95141050315002e40580b0784440c3c13000f00820480c02000210500001c1d10f00c41c0318000e005040220b01c181c104045000e040c1d6106840e003515042300f61000441441d071489082d68640414132411030102c5c0c170b00422007045000994045038503032881c100141003107201d901c40d0710b01c520100600e400503142d07081464222034001c80755044002c58050203031180e1003601c2009503c030785041034110034030754802d01070401d0360496030310100741322009034099907807090740800658940e0050000b000041d00c283c1182e580700d030b04840d0156440c00200030214800c1095003203403110070344070041c490f82c1080007402d202c400c1c4c4c0c217181d03100310609203511f6003400682c2c0608040c2c06640c4c031a40a420031b90048a42a520101d000000c568032044a129142c82c0c0d00f110780704400148200740001070b2040000b41080c1651240b040c04011511150303107185c14502541412418016001040e0b001c1030054858140010300210107030003008443d20005050140080c400c4003c40c10500c03140c44401c2d844002d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 30223332 1250 30222082 30222109
    0x121050d08040c030b19050604020f12060d02060408010605040b0904030806041a060a02060a060801090b0a020a0c0807080a0f05250f061107052103070806040e01050c07020a08010b 79
    0x140600d003500d840c1003140c28000700e80c01c094414000715091001e40d051b4101904030031070742440104000d4545100300720903031049a00040d1209000d00200b2030f85030040b002c507504035500801003060480f45601056041d00b09602102440e551110100014105130246000500d0101d40048062500f030350040d2000c84040c1c0500c2c0103940c0c1312411128050b445a5540c006440109103d0b16100c40540003591b6290032038141c1000303828000d00041c01d80c41406005e4405901007020095a5180d900700d1000f50810031030304c0c0400c28600b40c190080361121004140c003038081c01009549041560b0041c041c01052480300d0100582000007514030344040307080108101d4044034000d0840c4450420440001c0448070182807540751885100202503180003d02906204030107841d1106500b0030840c06921307050342d000c041004c0410000392414480c03841550311803801800054000c3c018220b050844408841c0701da0742c5800002e0701010361400e95444070080c4801002480003204580101d00510348013103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 30224582 1250 30223332 30223337
    0x1b0f030312020a09051c0201030e070605120702031306030507080601080606030a020c0a06060602060105030d0203190503180607081e01030c0302040e0f010504080304200a0302120f03040e0121050d 86
    0x720f2189641c07041800c240104070043ca1810104a07080d41c480e010500300790124086032802071070b07018025020800780c040300d00b1920342504091001d00301c1a04190700500d08000c5020401200314000b00f103200031400b420032a43c0002d4213250100340a080150050145818803181004002ea50759171041140c2c0d2120a030300c405a00d07001100c940611348404000b0040940e8105032011410641c002040c6049074400c40071113064080c1104140d8482c403a140030102c440040c1a2001c490078058401590800c0701c2409941e62444900c10060800313100703480301800940d420040c490300480d800c1545c803050201e068001171951440d03554007800503a07444005d01490b2203054019110200b4030005110741c844e51f0082c002450545480001c0b5442200c040318501103040b03102040c081109100f0140b44405440425924295000c128140045403918510b0344208451540b0f59082800600010140c00011845c0d83d41040e00140060590059030003a01500c200c180d80070400000301c6018045190 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 30225832 1250 30224582 30224587
    0x90405100b03030904020c0312010b0c03030609070c05010e010f0e0f03030f0703060308040602070504050a051302010e0a090606080406140405030d0e010209060c03090a05010809151e041b0f03031202 87
    0x1800843d095025140340c1661251011404502c0d0810100c02000c03000300482d8280d405070b803200103540c441d00603881500b1035903000340006400c0741041c81e081c5130094468208201d00203d40d030340c0d40382075601e0b1f8100388000c2e9460b840a0400a509030040c3d038001071010010744013800032000c840c2c0d038031700005010007400b0703213881c0c0410300b59802a401000615007000e00a80c0d0b8039114200607590b94254407449014070b1030440003c01c0302c0e005102d41802120001403000c060882c9400464030015030043c6964040a07082c0e00084007032151248400074075040d10340010700d140c1420f181c803c94a505120316404620207040000040e4040100ca4090b110024005204c2c0000300d00e5a0080c010003045607040b901c00201e1080502d0004054108804200c0784025001d07182e40044461110586030031000c3da1240060041c046c00e00c45d4070551000340285240d1008070a03000c0c0e456071103802c0e181940d0300c83c140006082080040300b110405049640000e1200c20b24590f00184035a411a03111104140c0c003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 30227082 1250 30225832 30225851
    0x609050615131e0908030106021203010b0415030f020c010b030601081b1302040801021602041508030306041802030106030c05010206180c1002030909280b06030c070314040f0e0609040510 82
    0x1d04540032090a8003000c10803a034402071411702d460368000c0c050000036100c3c00c10365a05007902c44c0120b034140e514900c0400d041c640340c400e02c440d40c0d05c01042010141903c48400d000050211b1000d400307000da0f40000891002d046500f45804c04406030411000c075040818610409030b6a0182c42c0e07840d110907610301001002d5420b01c0350007800303103401400c0305500025441c10081c803030000040c000b134022030341003224041600403007200f20380d40c0c07180f41207540060000440c549031650202d40c1044102000d02e01c2e5540d11fa00003401c480180e00201d86080f0303206400c2c019564100400303640015100e178802081d2494996043d45c0f02008040c83e4071510b01e4880e0100c5c0a4428015105c2d207240c00b03424809203050402c3c108002c518420800520b03583d41c2101c01c07072043c078680602c0410040140003507285445e0f00785221696800004190b083c40a840c003401000c0c41c0c144010401041c001c0e807039206503070030024100c1140384041c012511a044400500011920224480b90034031280340380004c04400c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 30228332 1250 30227082 30227111
    0x60f02030316081801020a03020a03051302010c0303020906090301060b03040303150e060906120f0a030e01050a0e0603041b03110307061d101206080f070806010f09090816060905061513 81
    0x640198042c131950010848010003034041c1c0151402c0000c41e101480948d0701d2061280400c03850107030180c005001c245103030021174000da000700109000680881d1600b0190800f02e0b00b035030039079486202140000410007040c907a042c441d42490211001504003802d2422000c0c03400144080d007207074403e00411b400700307a007965806103042090443d5015540d00320390108056858410448080d0302142c042800d40c0c2d01036104100300d0740e80d012107403118410380201c034080c80400d41000b00125900c1080c01d00c18882c1c44034011504008501c103407116450f12030310109240c1405c125600c40300a010070155440681200800701444a01054400e02d0181c0e154103030464030b40c1044501c9025a5181c080040707002503000c00c11070300102d1184200c03001e280c1c0d80d000203540c481d000d224010300c8601110041c85562140e8100b0005075002e001d14504204048502d81d070b014203640f10440700280c0c0d41403c9810007101344020750340318042e100e2600322710392620085020718413201c0c000c0da200b598600d6081c4440c2c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 30229582 1250 30228332 30228361
    0x3060b06070b090105040c050105030c1b01140c0a09080a0209010501080402030703061b021516270f0305010c0201090506060609370b0f040e0603010b090a06060f0203031608 76
    0x6811003002c1070141000304034503009203810b6805403a5501d0070413021a040d401202100e000b60101d8207031038a04139030f02c504240240000d11660740755549030304102078414503024003c0d0044540080b00d5a1701c0962010140c449002d9904c611101e811400b04600541e0f40e01c005141182c0081c20002240d6440d44002410055582c100810740740c60812440080c1081145480c1000019000c030b4410100545c2d109002c548101e54911915401c2c107000d40d8464403646440700103021143e0304445c0c1440303400c8030062040b0740d03400c23002c24502080410811b200c800d00a1f446640107900080084960741d4503810b031640402090f103400f030000001c0074841921955280600d020005000c0c900c8075203150405a59408118075a020265100b1000f042c5200200300300d561000202e09120f10b01860071040320f40c0c400c40101116819581d800c01e0b0440340e1541c034000351140c40300c08000250281002005060541c0501d200011075205000300001000008452031000d000340c10312846640d500e81021300040b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 30230832 1250 30229582 30229597
    0x21030813110a0e0613020c06130804030501060b1e070506150a03050709150501020d0503010510050c0a0f060c0302090a0504090501020c030703020a02030d05271c0c0504180c03060b06 80
    0x4200300b01c000514065007420700b40580c1c070890344007008407942d8043c00141d0040c1581c107400d54102c0e0f000705502128102c0000a000d02c03c11f51913040642c1d945070107084510a500407819602c0002d944121604208a240c1010602c82c0b141400c1000da030320b49642e6203074014003540802000c0300da00c094542d00c0c0d115200040d13602108403003c482e1030b0f0740d00c500981240e81c1c038a00205405140464250b0001c1042c0c51f03031258039540c03141541c0c42c0004203d01400e00300200750500c0002c011500c01c8030700611000d1b81443c0641c0d040179407403583d881c24000301c406a00c888020184140111301041d9582d8910340126101282d000c2500c0c000c0e82051030091140301c440010074480040d21200f00b54000c10141c1d80240200c1c00c1d50011100c1c200c05031514414400444903030648602030260350600c0c1070380843c10715805000340c58400b404070907410618409920549140020f00010085450700e0300601c01c01650003080c0e10f60f010150781d1414007a000f60f010050a0945940081065072100c0302980c407603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 30232082 1250 30230832 30230839
    0x50a0609060305010b0f09070c080a03181103060f01060c02190b1b010e01060b070b090c030f0f010e010207050a0201050c100203010f0303030518100c090314072103081311 75
    0x200d65a0303e0224000c02c1e0441d81d0502550840d5400319052901c114a1480303981d06841e80e001455150380c075240076900131540041030642d01e0007540c80340100540340c4254148504910340000c07811404151500700001c1604180c0e85a4900502c05c1c2903014016180c40d0341d06681051503200c00b14503a418101c0e0580084070a40004258001880c089005c007040070b01c01c40000300300d03078060036100b0750981d10280202000640b0800c03661001400c44031030203274040350350015038641c020302c100000d06102e1100d104004927440f2040d1030044250a106407105034100c00c0086241c58896600c1368bc448072015406814028081112801214140b040b01c5444101d003204550300e41c1c45e40f210515002842c04240c0010b450400040ca0742500110b00c900e10080c050010402c0c400b1404082e00a401c41e582c602c1c080100c0210300200103410b8580c1e44240042c90701c0603044450511400c0c14100546a00f4882880c0b020041d62002c03e0b00295010b82000590780154843c1d8214200342c0c8680070349410b603540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 30233332 1250 30232082 30232091
    0x50c01050c03071b03021908070303051c050a050702010b1807030e10020a02010204030b010605161202070302060c03040306110f0a0e0f10030e0c0609060315011116080613050c04050a0609 82
    0x135504030f007190007560710842d488201528036520001c01071505020b00880c0c1d0b40070910074800300e80114040c1214981d50416a8080304603e00711343d0940704140e4541c3c00c22a1560305002041d902802102c400103010389048811803240340d088a00310300060151800d01d517070b80811070381c0c1050a12034204c0070000b6000a665034155442c009000390b110388415203842c89040004a010b030310440448400f0207500c449400303900050f07110b4210001c1c06007006410f5204450000006854000c0903101400302c076005191600d145040c4a029034070001c240010405040105100080300d0030183e17820040ba03442c08075170400d14100860040e80d901e03440154020f20f4000c0800b546075050b000106c144080e0010799210110100a00042c0c0c0102c606517603100c40b060001074190100042800707004201454031400003440242e100e41015540101000100b2010501344407d031410482260843c400840c44100c8000300c0e200c1546072119048080d100382d803610045000c01c90140c0103a009000102c0d020003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 30234582 1250 30233332 30233363
    0x7050601030b07120c1e18090f0b0a060206070e010917030c1b0616050a020402030108031b060402010c110f04020301090e1006050906090403030e01110406030f0603050c01050c0307 79
    0xd02c000301c0c0c00e600050903078004c07411106030a0040301c617142d0058484041c600607814a804648000c0d03100d00c8108403000030411141052100c050008004003a0700245c1002c00840d40c200b40e0751001e044078042c0e8603c60702003000170350020b446540950286030241840e078030400101e9860595a00c52281c51044250050011002000500c90038011104072100d80b000c07210302d061141140003c055100d00140701d91a4a0000c1c2410031007028030900580341c15940710390020f0220780081c4c0044600b9400410000e55540e034070120802c010f02c91038010502440d00c0c1d070008000e940403401c010022294078440001039281c60b98a0403441c04000c0055440b581c58440000c02040344030308005141c410040340550280070b034440c041c182c4402800c4900d05030307112018090b0107031019000310304040e0b40f0301c402030a1030001c3c82000711b002e40385502155614906030008042d40c0d200c2c0e0042035140e28004041000400006108400344000c0c00c201d1344a0458540700c6045010303092024103074128000140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 30235832 1250 30234582 30234593
    0xa02130e100605060d0f0621020a0b0315131d03090102010605090412030e030c030708030a0b18042a09090506090a050d140409020a0e0103180206040311060705060103 73
    0x4400e144148125454140c40c000014151600c601c111a0480300c1000880315a00d41074103d01c80400d40c0030340102d80300380e661200304d9150403602c0c0c9a81d2000f810003010011480c00e030b980b10b030040401e03145590441c00c124103100c50709441400414403400608518030309043e002d411035840c140c5403c00300118101a000c1494507a801801194015460414045064a441010036014a0300600b1740c00d19896581c0c001d400030281c803444005e0610090201710348082e000c0005110036403244109940300e0400700800010b80e2044a041d51045407040f090501c02a1401481136111f0741002d20781107004100501c00e1144880891000c120a8081170003087d000303102d400c4032000c0c605c204216042c5a496110503a19000313800001005038000c8415550400d20881202040b0b1442c070a04078500350707942c92420300301d900010980300412080c5404038615a0940300b01510700e40c003100011040201c07540003403080d10890100514404400640d6101d0307446800035580c540342c3c4070b0100c0d0b00c5542c590405 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 30237082 1250 30235832 30235841
    0xf0b1801080105071b060902030c06040305010c030f020f09010c0303060b0c030301170d090303030507020c0d110405070905030c0d0812010803070b06010207270905030301090606030b09090d050304050a0213 90
    0x76000c9640c20400800d0440c2d01c01d402d82c12404d0840461003030740c42c0030b6540b600d01030300400100ba03034540701d914140682966482d0080005504c00c0c800000c1203104030710b024041d0346541c111400389a2040c84030b0714000c1250021613048140c02d1a000900010f9843c0950003450540c109800800b00444c281148440010007035041e981c1603080b00b102c1c40070204400d41d03103080300490040000e00d407030010000030f4025040b842e004403135801a915a204100041008058007400c1510310400d03c400003402c03420144a103540144192800301d0540e03082c81c020aa8410000305000e0040440aa00300140100001074541c80e0821103026006135a640f80380b50703581d401080d010b45603042e400001c140c0a40c0000741c0d2004440c03481006c40985d600c01510810341044580c807915216480395840700014a0070700055002c2d0084400c00030b4040d00b0030034010110782e41d50a1160103000c141043c041709000006400d000c521082c90400d580f681c0320710300b45090600c4d241d070003500a5510000b100041000750803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 30238332 1250 30237082 30237089
    0x6060e150f030102070c2105010c05180901050a17011b02010621050c040e0a0f061d01110301050d020102160303020606040f020703080103081602120d0201060b030f0105040f0b1801 79
    0x100110841d0885041508030711500c0002001d50f555030404208000171105100d0000c036580480039880003d031b4840c0c80c25200f1a90b0392100145000800d0034002000510a0000100c10340710010250b05050104060b82414050a100c0384c4900c92200c002450135000f528040041c10f8400d081c0610165020f406000240581c2c4800c403016035038110440050b0000302d4101d07402000a080e0001a1403c0c00003c011440e2400f400e03009040120740031036200c0410101c614030601c00000c1d841d091400105001c000b207816900d4990400c0010300421441c24156070664904890400d903100c0a403005070b1404241a003e000040f00f014800030526401140d0144286000c0c1c40a1080d5140791a0f41000c07407040381401400b03e444040148041a41100079021001d000070151005401503000158103800d02200c0507926032101c0c0d29003542550a02034540142172050050303003181488155500d102d8014006e060041c0e580e0303510081008103a802074880045c000e446c0007002d00c80201c241d035145d1000d01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 30239582 1250 30238332 30238339
    0x20d030b0a120c03110102060705040b03130807150b2706010e0a03060209030106050109051e0f0d0c090b0402030f04321c081005010e06070506190e0d0906080406060e15 74
    0x2030000c5206c6d40040b40c154072460069440d5031415050075084035441d0000b500b24003c1c1c444410018001070502d00c010444139004111030903030146061944000d443c54002d101c0d0181d49a24031413030f000581c01001d03d048410401824a2aa5030080122040054182d00076800380c919003000051040c55401043c0301c0f5000d800030f101c036030b0b1600c0041d141100644100c40c0c100c0d801c0409001800100c103001041d40d1002421010341c1900c20700000d800d03450080c4241d40700060b002042060076201d21811078150402d803400d60031407400c401c11002080004001421040503c103003807410054803540034402d8020744904180c181e5000e8145036407180e40c50300d1440e004201120a5842da80141c2099108125440d50313600043e080100461700c00450b0310781690080e10a111080c0042c000f84401c621601400d0250072550850440030010341c0c48541e00c20049030003d001e80c041040d40071a495041d1040b9051100c3c031503d030303840c000e402052036034403005081d1014001e12444040e942691520460101c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 30240832 1250 30239582 30239603
    0xf030f0f090e070503070905100203040905010e0603030702060c0109020d0c03031206140f0301020405090703150b0901020601030204050402030f010504120207060203040506040302211002120a0c020d030b0a120c03 93
    0x2003a0540d07680c0c41c90300802105010340000a42c0b41c2c0c0c03080000319481652864105011f035a1440071a1003800c1601c00c81d0096000400e051180d0282c0340b090a005000c1d42c00018002c2c103000003c071741c5030320940d980070340604000541340250b088250841c1007040c3d030240901600001504110304810050302044000070800444403800010900598094070f142d030241c41c80e850428010091000318400c0c0c40350f0155001d101c0080c490f552102c003648600c0c01903c0100b585401e240344100f544009030445180c0305001d0100206c40d903400551141907a5054400145980311400024540360480101c2212076080c00e08000800650b02c14040d2140c0d050307000c86061703507282d80d010b9859018500507250002400d2204102601e410340c0c50524042d80c000640481c084403007180c50800d0071052804400340e400196a1059044000c140d0354403441c0410104148440100003e44031701c0782644060030152100c00400f965516049481e0091601003000070f2101d10b545000c80c0c0710304c29031000f9903c0100f032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 30242082 1250 30240832 30240857
    0x71d04020f0907090905060307030c0905010e070f050405010e06070b04120813110d1703131101030501080316060605030d080a05011a07320307050c01030b010c060504020d0f030f 78
    0x20b49110b018104076280c089a16003041c9001c03005140040c440e6034188a0400000003281a00f640b01c005400f15441c042030960400030084025a0050080c5080100c00f608103032490794000280c800742c4509281c042902071800c00002d00500518101070a4212110140000c101c60701808080040c142d8644220550b610380b40c5180c00f440d0714a01810080d240c0110200a180808082c84442d22422800300084080035540490760000c03142e0f420381451300c10421302403002c10b43c1186901700007484c00307020a60501d422113490303000b5414488040e64840b1800c004100b115000003001d460090300b15620308000c4040144005020788a95400382c4c580b06c00869000d015030010311020459080c0c151030490b10751b942e8010091041240720036032141803002c0615130340070b10181000801d04001144ca460060030110b051192421605051600e046807601d91a40c101c03040b50142c0340c1000002400e0780d030300e001040c1021041c3c2e2004003485440100441010740110240d100c504080e079030001800c0c0b8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 30243332 1250 30242082 30242089
    0x90c0203130501110d05030c12010e09060c03071d01090824010b0702010903030c0302010b0d0305040905090c0a090b0d120917010203150607030219050d030b03120405040c02071d04020f 81
    0x2400d01070a11600170200505600d80240000d542200c0421421480c204e1064131044894400307800c600c84401f440000c1c0051900204a80c980040c030180c08541355044c0030901500c1c0900f50f0f010b40b200964110703151440d41e80140f11180040c0240d00c2034a01c450411103c030012080b13100c40d241d615484002c008162a40794a0070749402a6068580e01c0c89941503407015030b2802455082201159210448800c01d511081d02c03c4000903c29140c41fa01d0798204030480c0d040d030303200600846669014100e1003c8940e41c90089900b1a40a41c6001032940e0004001c100c0c0c043d09100c000d820250655400611140d00c4100e120840b02088145800d075000141c0241c242e200c180d649c003403890300850b14600c00e480c2c407000070401940300740100c940591040305510540072007690140e46541105245202c0150540200e00180100703e000d000301c0400302c20070341c0707041c0a28003509000d66522204100814002c00044010b002c010f0600c0034141c0309500368070509241294202d00030103018004410904 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 30244582 1250 30243332 30243347
    0x30603050703060b060c010606080414010b150d090503030c030919050619090b040b100501030e1903020705030303090708010b01052503030f0e0c090702030f03150406090c0203130501 80
    0x2a844000760128920316107a540244c4404100d0a620040810441e03103541000d12910000303100d60b0b100c0002c80d01c0c0a090071076515022018604050341021340b43c070b20550724901c0d2450850381d40360000e6140e80c1145000b000400d103030382c1c00070068030000091140110510020754071074120340040b540748110090002400d19840c1800914580c084800b1401030311485200f040a000107000008001c00c4589507404072031802d803415a2007070b07142d0003440046004c0b0145080900f00070300381403140c03034620910269507070741c24800c00002d042890300b0001010710034070008004200040859440b41000d80c01c880d2521106c1c841e4942a41c40e041d00310205500900942d6001d02c11240070500700034400807950150410780c0c1c82101099038071132200c0c210000603c114405000c1280c0203001101c08401070042d82080a04601e041d540244620314551700c200d0300301ea901865103100d6228088151000c240500180d802513a145c505248188204039400000341214119601d107000e8010360701c4006641b2035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 30245832 1250 30244582 30244589
    0x1006050a0203030711031207030f0e0c03030702010c080706060312030509010b060306100918090b0915040f03020703050303071e08070e010f0e04021209060a0507090509060f0307080102190306 84
    0x60b001031001441c118000c0c00d8801a02c14401d00341d07440c0030f40103540311350004821110100420350b01e229071803810080c1d1140c0c00020a02c0c40c01401d030f406e2a03800103540d07402207a80003810821200005010440107506484060703030300003010b02c502c94032844c0003400b010700c40c001030001a140c04005450441c0c14000c0100d0704030f0142c105032658980d0410b02201496410403d0b081c0458443e0000b90164400a14109180440000541001986442008560003a0100c20143d02030440740b110380d0103007080309400c6035101d0144059030480b460241e04040c2c059001070a12b000220801c121180c010650001c0c5142080840984003401c1e0340545402400b5a036842c0040d480e8851902e195026011248004d01c50382411810410340b40c0000d001d07a404201d441c0c5000c110310040c0f040c080d600704a05500110482030900c442d180030302c0c0050103a005071048500c10f00c05800880d20b991103440c0724925090700a0f0a5401d507a466104660103503100c6050540049600c81e00041030b5442032150400b075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 30247082 1250 30245832 30245837
    0x5040201080723070305070c08070f0b190e2b0c060825090b0d090506010b0304030519090509090a0212030406080a1a0a0305060702070509010b070f080c010905061006050a 75
    0x255000780c20b0f1106410007582141800820032140c1c0c0424829001c44008010880040032620305212409010508692000b07071064810711054001c00300c4484000c0d1040560300d84814403020102c0000e90a0607001e082000d0b02c1c1c448031405012007120080320400500480d500d0000d6640c5240c203c405070b00488020080c42651401c1c032400b00412506800c03024064902084c1c80c075140e0241021581c401c0d50002a590b5031881c040007004070a11980d40184414a103203800c524003a100a4650700c641c880601000501c0030103148182d015400a80240c2806015480b45280400400d951024454400d80c861280414005c0320f149000080b141507030300c20b54502e2020348990203540054460034842149808841030460150340b24003120300000c41c002d90040c00f160401d50700186c00c001460700014014080355005025019001040300c0307509038000c00003d102005402c1c98103043c0a9101d21014650906606405100000480c0c071b004107204c0c1c4048030165641c0800b40c0d51442140c200101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 30248332 1250 30247082 30247127
    0x30901060e04052109010c1506050a06051e030702030d0b01050409021605010b04050c120a060302030f0a03080f01031106030405100e10050f0603071509030c0605180f0108060d020a0305060a050402010807 89
    0x180c01000c3e140382c0301108c4402184803500c0700c00007909c111054002c0e20000c1c10104101900c26901101c500f001c22a03601040e1441c104100002d40b20b2059070101c10344542c84404607160341e441075003150300404001c0e00441d114503684500550000288030705590541c01c1c410039440d1031419101c1c40303002d40e4090450602c0c02e600d026084200920041000c0c0e0030a60b00d03140000962024811139418511140150403460034a240103020a80301414100030500b240340180001860011000b05030101160040e0312a552031411500e413600c0000010319080c2041450001903200040d120480207003010140300e03a0351000e270358150007103007203030385560580c4454810821806c6485190050303001c0c03490115911500c07500c400000c2070203580301e0400960001101c41002041c00740304143c2020485a4285410005000030b042d401c0241c0000d00c6408407903404001c564407211500300840c1e00c10151501460720840790302c010315080b28144d0200d6000400544124811440d03200d181401500209 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 30249582 1250 30248332 30248357
    0x60714010501090617010b06091219061512050604082203050d031109060d05060a031202030a0e0d150507120615020601050a0b07030c0317150f24030901060e0405210901 74
    0x2801d00c110300b07040740b079a0089010be01608400d98182060b8980030f908040361241807260900310080c03c540c44940c05a030395151074000124040303038281d0841d4200c03050380d4441d02d80c041e005000400c003503e0000d4250b01e245000080010214007040d684296840822a641c1e0010641515100780c454035680107008000d180140d010a83c845078205002400003141e1988a1742c030041d0140480410070b000d680040394a400b440d501400303085100070b042c1d6040c40100c1c1e640d40c0e030012070f15042c40055809500e0394001040c080c425110310a058001d4102030041c9940c64100041c104410781c1e10ad0014059580081200d040515800b4122010f81c0d14003490705d2801e40f4101c80128415030110100b100104403c50a00c2c96414a1030182d030000c00f09401002d980c2c402c000a42c1c0000b00140c1c060301e2068120341c4c2141ca07969a08040070b0320104103564943da0003170580d0040440340c0168140d508800c06010a100d0000f5892181c0703600041340d04543c104180c200300e610701591111500080e003c580c0003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 30250832 1250 30249582 30249589
    0x9100207030b100e0a1a03030f070611090310051810060f0e06030312040206070206030f0601030b040b030706030e0a0204060b030f06030109020f040f11180102120901020c060714010501090617010b0609 88
    0x1405c0d00c60f41203030855401011b0000a41540e011210f41000e81ca40440e10a040c804c0380d11400c1c0750342c0b00c00b50415160500301c9001ca900c4141000c400c10310182e860000841e00002035604034207501c0190141c1d00f10702c039400b00300e400502c0a8080c02250b68120580030850060b11749046028032001802141010300030b03042010417020040049070011000c1c0013801c0142c4852002d58014440d540d0140391614040c000101122a8010094803070b90520b009105280c43c003040101c255059841d000c1440c01d90710400b2032900f20b0381480250080d217071a40001c0c2c1e501c4c1c45e5016600846030b98580d00c2880c1c8a0b4801c06082e5911120b01952040a444a001c2d080c580342d40060350201c1e0a401c0030454022001001c12140c000d02143c45120f14a403c05405a41e0b06018540e010f120b0070f00d00d24100300415000070354900041e071400c0c0c02007000082c41024021034102001039030392070310000c5c480e40d038544140c00c025044078841d030500041c80903410200e01038180a281301e6560b001c0d141c2403d081501041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 30252082 1250 30250832 30250841
    0xd0209060d03030e03131d07140702041107060903080117060f07030e0a050601140a031a040f061a0a0501021c0806280e0610050403080f09100207030b100e0a 69
    0x44091596a03a201000712200744060800d51400d0910300400750b240007825a080c3e4000012904e01360300c181c00304545560400c0c0250b03c427480685809843d600948003042c02040f18964902464001045080410070282c00185d6014445d503a142e22030b9a07074051032108400d42c5800f400f295005040000c0d010300c2c802225541c04211441c021900c03451510041e810000f040301d050380c1c0d030382246006004008401c01c0d410390269040d00c51840080c655142d64410070b18520003000c000610002003000e1250b1444010b190ba1f4102c81c007082a048040b00f280c20000c9600e044602070706d41c1c50701c0051250700200d20050100c100341c2d030841d8500e02c108011540070400410700c0354481c1050000e0241c06030146011045400f82109084142d4101030340c01c00c045000606540c4580b240390344e24201c4541c818191001c40354440300f007a0f01e07082c001c0340d1090140030342d8040d25000601e010108006581c0004c43c4000c490040314000e00b02c1d16002040b0580390702500400d0b414682903008a044c82c000703a0b20 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 30253332 1250 30252082 30252109
    0x20d0207150e06220614040507080609030403020a03120c230105010e0c09010c15090507081e03040608060a0506030403030b0f03011a010e0301060e01080a110406030b01030312060906170c0d020906 86
    0x40007401440c0c044041b0300560042e50161416440000103210120040190580140f2184003d60410746164001898000107010080849000d00d4224401c01d004000c11170384c0030350003000d040040b032031503800020f43c1d04200940007242d07091500009000000241190280018030201c502d82000607006450103134080e4011540200c0030038020141080070300c20304405c03901c05d802802c6114604442140f0308006001c000c0009080462400302c0020000211011502c0604044805603140d03000900100344951150703400031000000c00040651590291480000403035051060721446000d160807100e032840507410041c00b1144c00005d035030040002d104910001070020510644649104032600c1081e405030602d2b2303104048040030050802050b24800da000d403800c22240b0b00e103848102c00940103100103014060000d41610a081d125004100600751460080c06520b0307a034030003442d040b00c00c20000b404a010390310940e40c2c185030030710001079040e40080400e000c82d01d07058100070380001c0303001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 30254582 1250 30253332 30253343
    0x3120a0e010c02060d0207150c0201060807081203011503020403021801090f0908040603090f0c08010e210d0903050c0a0b15060702091b07050601030f03080702011b0f0201020d0207150e0622 83
    0x20b0b519214180140101518902700b0b900102d207092410281c3d514002183d00483e0054011343c0407c80b034100c0300030640c0e04407031303296582002102c07003c1300c203034002d104076000a034010700100d407011201d88440341c01504039443c4210800054600c0d0000000722242c0d00d0008140c0441040100a40ca210750000d0b00414002c90201c2d01501d601e642d0340c0403d5407182d00050a0340d44600384010038090501c0100d0480800d00041800440c0b002c00001c2e40d48a1018200b01d51550752190b1000d05118200b561100c03200d42e002c95541030a0743c00d00250800c011a40000641d480b82071907816418180107035418141d01604203c0141c841d55403180301825180386d55080400213102030404110f08220880c000c60040d01d0702c2080151a040080281100070034200c296070500003804011a0b100c07004040a100c0d610309040d120000a004902910820b0404c07611540045450b40a02429513201003071403000c40e1082003c018000e5040384c5a090071141d50056814095020007a000134003418004940f003107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 30255832 1250 30254582 30254603
    0x30d05031914042a05101205040302070806010b040308030121050307060c020606010306231f03050603010b12030a08130b090a06140c0a031a03120a0e010c02060d0207 73
    0x5070301800448841e165181c0c0040e0101d028403042c0410780000601d6060420420020700880c5101003030700b000144a413a002d21100301c8000c2100c1e04c180d1400364006007040060002c0d06003400e000b5070368a00c501071056180580c000000c1c1611030132049030704607544074100c0b5003960718200d06420072055403a0b0380d88130004040e8001c0e00192050004206403842100d00240d41c00380e80c8030083c50007100501181c149443d0000c18001c0d4001c030b0200110741c15000700d1510204c4446000702d4030403c49900b0403000e03150081001d0000e50b416401c81c5205030b8054008100041045013000300020005140e5511fa800c20086141114800c07030744d10380e1110403941e00900d00c0a080d510045200307422511001d10745c1080b21940200300450180c000542c030705d40c40c11003407418075908082d1a881104200c100381507440d030380718000e03c410400b070360a81203004090f80c5107413030070038000c1c20240d101c0b4640300006600001d40d100710798041d84e083d4801d69000b030101e9052a6034140b10100940c085441943d410000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 30257082 1250 30255832 30255871
    0x91002030a0209060c030a030c0c020d0f0219080106050f0301020f0406050d0605030a030503010509180c011d0301050f070809010608100e0a020a0b04090c11030a0503070c080c0319020606030d0503 86
    0x2100c00512941403003600542c0c1e2960113210040827500c17620250820004440c0f60900541d40b00085000520b40048120301c140326a48001584840c0b00d0342e4007000300c00c3c40900000d0102041d80a44101e0384145ca101c0741c90481e4202b01801c0b407141c41c82051030030310140414025540b103400903200c08120300c0d000095040e20307000001c1c81c002c0d8210044002400000040c8083d040c80424503421a8405501c4640710358400800d54072008240c413080d0400ca80340003240e2044032600e12104000b08050300800c203904040c600d018042d1412076015001c40e1640c40800c00322001403107924100c98840015090540c0401d00b0000640002500d000323192140c4c04440300075a0350164010300130025204140c2e0348a151449410a1700c00c0039141e50203001c00d0184d000100c4001004554181c4100e180441c1d40c0c1d550040b06942e4400c8419010306003110100c0d4400001e0000001807079040710040c4250003900ba5010b00320303610b150844489803da04910203045546001e10069500007100180710740c0c000c401c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 30258332 1250 30257082 30257089
    0x5030708070c050a05030102070b0a02090103020714031b030307230f120709050103020403020f13060f060f02060a0e19050f03070302070f06020a0b0c0307020102160602070515091002030a0209 84
    0x1181d48140d50a400c460010002da1404211180c01810294025800c25100d03880c1d2000204005001652079500010b05202903031203941101c80859001581e4000080300d5200340ba03803600543d8082c1c16031705650500d44c11100002050300d109802c0d0350b40e071100b02013882c206a0f2507540300b00d072141e036403030818408120380304249005081c0c600c2003000d92441911b060748004001c40c1d0180d0243c1c2c14184104401e01c05a00c034070100e2140910b0603650011100c00c0310000e903009010941c40003011801340d00d004a21254030607038851600c009035003194840c3d01c610300703e04222400081c59103111341c4031a81c2c8011a80008241a001034040d0042e0b40054507201c800a0440d4070114003140181c00981060010307a4041400c07502030242840109100c0d5507075910300f2201403000e011020140c2021000172040352003501203801d90220391180351b0711281c561412001175044a08111200c1c05681d8000380308040f0002c3c1c2c68460800c40005041d5588140c3c2e85000079480a03000780110f0360208040070b400d44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 30259582 1250 30258332 30258337
    0x9010201090b04030c0c0905100506070203030403080f03010f0504060e0112021305010f0501090b0406020a0f0f021305090c0405090309130b03030301030308100e0412030f150b0a0306080109050607080405030708 92
    0x1806916030342018601c0d480d0109046e40700340c00540c112440c0c03038180110760012002c614284d82c006c1d0303002070b41d44025000003861070007641e100505480c0300040b0444e680180a000e141255040310005003041d40b550100001d0f07814038040c2700c1c01900c446004011802d0502200783c241307030010f00040d9800441d43c601a0580300240c2041c821b800090004000d076581c0b00348144000c00340da0546c0c038101824480000d48481e20145d01401c041400e41c0802c090040d40c0010400c4207500070540207160000d03068820107044e00300c80c1d003002401a9a030900c0c0c14201401078074440c4030020091850f01104a0420401c0d00c10710204514003540d0702d414581c940c5081000b140030318000d03140d101451501005140890802d60865240c104101c800c0c00001102000203c131103a049081c007240410707000314200000d04105c0c103128404000d6007800602401c000004207010307401503505122050b210581c1034240d0b024460300030240d40c00440055a00c510451b006504244284141c92400d090340e1102c03d41038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 30260832 1250 30259582 30259591
    0x60501090c020c03030301030f08070c080d0c061a0d0b0c0c01060e0411030d0c020603190c0909061a070b04020a0e070807031b0f0e040b0d05030414060c0d0509010201090b 75
    0x30380e40d08501c0e210301e5010810480f851108400541c903640c1159200050302c40381240080294801060070406c000c1c4034050f80015005000403150784805e00340d402804031010000c2568064540b0194400c1e5820381d402041d076016000d42015101002d65a45c007910351001840c01e910312009100a44051000380141c100030400c400081e4240c0c2071600b411231800c1c1c400b45031a882544031010b00d40303245402011040003a501203c170700b610f07035948044a2001e21184207140003503d00e04007031592001c0c0c2010500050724881e040412156403103003a000000747e00d0401112603807200b44072800000340c5500c56540d100d48040c0004104a41d6003c480c11500c405440407000700705002c003042900c035814420b16035043c01c100152014249220009007420080740f8019041206000c1e03004500d4503039800c045100203000d071608400c1300c01420080d0f140e800070300541c20200c0281800110624081c026901041682406003541940314041522654848490740d03065541341c2441070301003440044000e128 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 30262082 1250 30260832 30260849
    0x8042102030304021e1c020102070f0e07080106080606160f06020a09080f03030112020904060b130f0f0203010f0b03100509010b0904050601020114011401020304150f091401020d0302090d060501 85
    0x41e803d061041050807480b8888070304514804242c12011541d40589000a00b0200d11404c858003c070703800101e0030003000350013000c288004100c00044001c1601c0000d0300c94886652140b0050740c803000b085842c0481960840e9106406100308080d9411355070440340d01520880c0d8400030f6103155034507075099030480b0200c01d0205144010420003039006001e0a00710001c80303405035107103605000700c1c5a8220038002019010716601c070300040801584c1e91143c2c010342c200820350200c09011f28840b2000e49072020704d0600e0320307051034141b60340c1008500a4a042e0b6400360000500c442c10005000020380008154513030382095100300081a8440e500481d001c1c21000110030f0340c800308442403100396400a4000360440e0715044c5100c0d0410907001042d810364070100484007a80c08401d0040380345000c0c0c0d030000f82c00c400c41c050b0800318442d0005c428008003030082c0c07100360100da0f40e40d01c0940d42c0c000e001038490140e0012522184a02d00c0707540105206900189502c4107540c2c961243c10488800345c2010f4034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 30263332 1250 30262082 30262087
    0x1302130807050a0b1207080603010905100c0e18070311120109140c0a0c12050c010e01050105010305160906050313080a0f02060c1309090609050f011a04060806070804210203 76
    0x105041001110010b040143c540516041c1c03840003a045c40314004040c0c004206141010440507642034106e007145681000c11540890b20741c40710500101202c44400f4040341f0501901e0080b820b04441d2141001c04030107002c0704d595500c01c0c090380a890480701841c1884000c00c8809615244002060301808908000141c80021a0100e9140001c0a050026a9142800905615a88121010189948042c0b01d50241d0301c09101610f280c0506450041e2950070701400803059007056000034101c6100b641d082c080c030348070804503080300401100140002419520144412030084000396008a400a410711000b485511804070580200b8808000207401d5000c19440c25410003490380c0080c3d007001050324107004002003001d2021140b2414140d03c4d01c4003070103001c1c001c0641c4030818094000c070a90f500342403200e1002d402880c0141e80903441d01e5101c603029619081a01c50103094500110041081d901c1d2110155082103004008444e010b05480001c0e114080d60318403560001c125400640c1c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 30264582 1250 30263332 30263339
    0xf0d0204151106280b040605100806130605010c060c02070509040f030305090313090506030c04090b01061103090109091802060a2a030c0206070311010606080a0b0d0507051302130807 80
    0x203043c1080135101002c1d1001a910242141281c005082580d91080d0f1000030740740b1003203002c60041c00319030303015a9111002070b00401020360810300300f0f0310480086035807000300754580c115101110701ca40603540c00108080d2118000071299400800e034010240101c424580c1e0300d42c001350900381304480407116000001c4000d010180c050162680040c1403101540c1000301080b8101442400d52088044258071500070030020b4906000120140a014000b407026004a042c6030840c041e0a00c5401c001800c1301007145100d00002c025200780001c142c0d01c1100042c60100040054064100c010300700b61050800c000059480c43d00074020048152100001811302211407000380051003a2410702d0301c8910301c4000060342c0005034108080d03040b6240da84400c880d060846150101d84840070035907281500109410381c001ca003151090042c050144210b0240c0703800e201d820300301303020001d2090b4400c18060209203440c411440381124100d00040c1400007a00001c6c07066251a80815505c1c1c001c0e80092 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 30265832 1250 30264582 30264617
    0x309020f01020601030209070507081b0309010801120b06040905010b130614010903050703140f070b030f01090209030d031d061003050f0f0c0105030a09020904050d11010c050f0d020415 81
    0x44a0030308240041c244541c5580c011030f5508400030820000c02c080000e0b050f080004c10003e0b03070544020852060240b004c4c80c03000d5540c07039102ca0b0b500c41c086418600005807000d900200041c20540c00860945582c4400050002030402d00d201200ca55403600001d403100c5e00d51034001040c40e0040d27074000c5030061604949403d00b030607000f000c50421803c40d100b0b0010a10015a100450798000c265054851110403064101801d04410102a0044450000740c0780d0808010718010500041164841d0b6030b180d054504034070411001c05d800d500b01c0c030081941170303019502a10b403090750000c41d1a00003000820150030700d1000c503200101c8884c0800d0a1051043c02c000e80020440024000d0405020309607c0543d100c190300311a40c1000710001c00114901140c1c4c1001450b164003030300442047c02c280c03400507190f4a00d044840d00103400e03a51803065001c414041d00c0311001c01030300da181c9012030800320704040d6401030072082e00c46602000006040c0050410050040d513981d96010f41034209010f00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 30267082 1250 30265832 30265849
    0x2040c17130503070f02150f03010906090614040b0a09090804030b18060f0c040b03090c04050a060f05010c02061b03040e16091403070f06020109020a05061206060d0605040c030902 79
    0x241521120303807a010300300046000044402c4550080042c0a4071081440001c19510b01d4980840c40840040b40c450303001c0c041000558182d5a080d28240030107910b50341c0c1c82c002c88640f0b1082c00b01e11040320740c0e0840c150500b948100c3c0303000c1001d4440101c49032202d0055042d2200742d04119480140010204180300110707071019001041c2c48030750258100f401d00c119079100b40141c0481e900d034801d00041500384410b403007100c0c02440e1a01c102500d83c507080069944480340c5068043c001c0d4108400a40c00c814248241405d59441a0448001038141001119054400c88080381c000d0400c1040c0390807403a0b0003c8803030503c152000150fa0f25414115110701048019006902c228000c882a14001d42c00904038001c0e12440c010305044031600700700081c900384065201c907103260300c4590046691036043d0045248240240c1f00b0103c280d640300b0a10815118200c0c0881c8800403d5010510790305e00640107143c2250b03103140100e455030300c45001401300d8207030350b900c07a0210342c3da05142030460038034065 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 30268332 1250 30267082 30267091
    0x70e06030303060a17010216060c030b030a0510020c010624180f03030c03120e06150105130b030c07050d080f0108010b01090e060d0c081006080d090b130302040c17 72
    0x81c50440c01c0c20030102d24600d600703010302c1845585c03102100e42016070941c15078034201e184515640c448103440c10440000c26607001050b0020382848055134a500b00020741c411156071200040003201030680c03680000750030100064226548034a0006030003550184800c07034a41400384c1034801101c03500e5000e00f401e010070411642070290007804014513140f10b8220b00440c0d8140c1030a401e100d10a280458134080c001e0300d505103444c5000001d5000d90700002d0340034820385a01e0044050000320340d00644a90042c003440030a040b101030024420b043c2070b60043c641140718881c0c0d160900001c1d503038250416042c140210b0010747c09400b04841c141462030011300400028008116170200040000e281d01e42d0707030040044e4407c68101256058481c0a1103080e003540044144100985440f040d6071102d030a0011813a842c0d00b8003501192441c00403a45000d820070540f0f505105600c0d11003c0115500b01c10400c00c221003101d8800009601d5501034407150200e641e0b110801500d03649442c1281d10740103030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 30269582 1250 30268332 30268339
    0x905100f180302100b060706021201090e011e0903051308030306100306030503030f06150c15060102070e150604150807030c03060602030412020f040c050309010506040516110c090702070e06 83
    0x441e40780402d80114003054107408089010810008a0010461502c504900185414800210540c5440c078500100341660380c2900d00344940c00d213a41e201d9099a048080583c05602200c4455040000980c40440c1e26446410103a00305280303074440680445440c0d01042c80e03500000208140c0303280c90850310f8010207a81c00d041084600b191581e0b59a130000501c14410841c0250109040e6903075000031800c03191440880c95a0303158001c0c1d095440c0c070300903014820780c00c0350100070602540c000b20711401a12035080c2e2203150381e500c1c40c440c824242d0440521a0300701c03104210109507140e0020302c070402440607071604040c0d41030007a0010304407241000b991341014a00041804100d03030110850342202e01c0000300c410007075120b0000491082c0105e40b0a5400340c6018181404150808007842c0f140750428000c00c2107a4404092100b41c903005c940c0c0082405140b28801d203828041c540b5401305180d414215001140000007140240780140c61810161b4081d1304204284100bd441e1180c4c401c000341c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 30270832 1250 30269582 30269621
    0x20601081c0507031808010c02030d18050a02090c16110102060703060f090c02030f04030f0309090902060d0207050c220609021207030207050a1203140f040b040212010905100f 77
    0x100300a096000e44440101084078064082c08117400c1c6070081000760882000130040d900e480e00002e5981d50011400c00c0c0440d040110b200040910004440906608103015054405e915401c0140107040103104c4c103460b4005015401521442e803c0700d96002d84103908ca54822510240060728011000b48400700b00740c20400140f08a4054000d42021510b2040c00440c8012504000b60709500031501d2400c841c0c1e0010a0010074400c0000d03590703044034080d85480340e1160f05c0700141000d0780c800e030314046d400c42400c0005444241c0d690307004140e2039014a003039613240c09103000060020403a190f50f80c0c020800380c1590490410161083d00000c11200504515110184108444c00c1e80010301603414942c2c00b040c01d034113102d014085d028040342d1081c0310801410720040e02034020440720ba0000700c000c408100182065480b22851401540c010b40244071669883d820005e102c410410610b01c01d54a50740400001902005030403035604466102140c44401d01c80309804448030860f8110444400c0e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 30272082 1250 30270832 30270883
    0x2070e0f01030b090a05210d0207050106050a06170f040f050303090105060301050c0a0801170f0d0903120e0f09091009050c040c0c03090902070303020f0403080c100209060d051506070302060108 85
    0x5100f0f1031041c0c60151301c60001f508660304001c18041d03801d40d40d228900000f10f5404101040d0302980c107444040340d942c0f01c010303100c0714121400b0b2400181c0c0e600e140c03e0070020644000d0700042c01a40300d4804c0300c541c241c0e500d46a40300350442d04203851420b0240e44880520101d8a030078024070340d0103461010f0040c104400458000c03c5084188507030054140610002c112101041c087c0b10342c0f4041c000102d400e29200124000d041ca0310502c42558074807081204070082c4c85c803802e0300c44d6204000801101c00c1800f0541089840303074004e03108400603c0b410300b02e050f4442e01c90050380c1074280500068202c420720b2400740801c1e01d80b801407200c104400f40c488100001d80142000b0300782e4040c01001626410a0f141c241c0082c0f041c0398500011801c003084c0002009603504c010080100b8050555189005081070001a4050340b1403a43c1d00141c18001c031205103030260f10840e4059400145da107140d5140c1804101640c0c4a2030b010b40050b006680140410102004148140c508090095107031104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 30273332 1250 30272082 30272093
    0x3070f0e1011011503120801060503010b040519050306161709031e070c0f080f15060d03090b03040b010e0709030203100b010e030f0f011404020a03060c02070e0f01030b090a 76
    0x401019070002d0000656500e0003441007503005142d801031000c640e0240d1a00d80c1010381e6283c44064800d00003800c0000082007461203207050307078101e0301000030a42c00c0c54200420030040e10200e0503850080108614002030700d9504000690242401040c0341940d400d040300d00078641118103611507a5030114805006850300c3c0082103900e41e0804504110860300481c84450591041c0034028125101d026004500d05035180d491a04660901c4200e800000c0340c07020490300d4040030b180c0743d4400c01e89240001c1840c1044048510414400e1418010b002d4030380240da0f48170740060320186e03003117003000e030050001c4850909190381044882c1080c904252955002075500c414038107048010340e41764400031400d41d0154040c94065400201a6980c2c103010705000c959800785a80e041c00250700700315500c001c000c00c1030100c50190f5005000e031404a0304584610300034040c2602c1910131480358110000300300c400c441e90ba80c06655206103200813035240d4101a503101202401c0d01115070010022200005d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 30274582 1250 30273332 30273349
    0x32107030302090a081204060f080405060f0c040305060a0c020c010203120c09040b09150307050f060415020304150203130f1206091112010905060112050607110a061103070f0e 77
    0x358145000741e0f407140c1c52404250b4296603075225104521840c0308000384503d12002420903200340c3e9486040086107007100302c80c0e44000f0b0741c001e44950403034000300d64a1000182c1e529804040c2929440c40d03d552a030707400346019000c6500c48085995106144070445d410700c0030f107004000910055040540c3d2a00302d80510070301400a044644002400041c561503640203100032400007001c00c0c90b185803500f00410074044016929120380034501b4040742502d0b00f0302d1510445000900582d0070300e400c02210b00044c183d1b03000ca080651000384800a01c40c0560118610656a140e025580300c1e01d0402c200340140c4e5640c1c0124144401202041c032440342c640e1a503015854200744003007074030981418010b288244103807800d50800c5512810080812054010b1480c2512805c103c440603070341c4003203520542d050140001c1054021001041d02181b01e40c05070007102a844095869403000d640c2c941c01290601d0080da810b0b180b01104020f04c86403c80e03207a108030602800d1050034038142c20700180009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 30275832 1250 30274582 30274597
    0x50115050a02060f040c05091915080a0b040203030408070602030c010c030203070c0f02040b061b061602120a1803060c030b0d020102120c0c09010e01030506180601060e061207030501050321 83
    0x104e00c0d0001405102403c1c4500c4020700000c0c0c8105180d04080120300341d400b17a66001c8c2801386003041c1c0c03000005601c2d075030100111005503000c0c1190f84801e40c0c4920307038400060001c5e603040c841070001051406042c40150001c0102d90021681c40d184072114509440e180b00d0400140752060040201080e04065002000366101c10503041f805881e00c00240107113040c80500d900f050000c2050071692801801c075141c00200041200c480342c0c1e49a407001d9480420002160040c0c00246015030a162aa00641700100460405014013255200b505100914079481920213a4950081c4103201e50107214088008809482d0003029507226000070f5607804180c04442c040311400901c10221000074171480315a03440041010300c8959545011605507003080c08251498003411000c1410382c1d0010b80034500402c0c0c1c10020b03040d503038030b003207803d60341600807181c030746d412150402540154000c10344040d80320305003a4900203a19410601454500400140e100100031403007519990322445100aa4021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 30277082 1250 30275832 30275851
    0x1080d1b0b06010314010608180712020105130b030c03060a120b010e0a021605010b0f030a0309090f0e0a0b0106080c07020303120601030204050303070b040308100506030601110c1003050115050a0206 87
    0x1e42c450710012801005070070300d018080900d040002c00d2003680910076a009171044021690344988151480342c8810380c1c0d100d030480c01008100441b00550080000e042109480c40400b44600e40d10141c04a5941c0b0440c0e070701c42c1c02d070030003c1000310920306104a04060700f0401d51504940c5425030b0360150a0318117008211402c0304a10000c0c000a01d244c04540c000d4940c12900d800c909081d240440c0640b10040c07046200d03512161481d6202d04000988403030701c9405075200c0390b407a4500b10034040242845507104044a8403615514416070b402c01c030200829124100e1100f40350715200c0020601c91010303001c081168810010380d000f60b68004140c071340c07480e03010140d0003040e2181c00041c1c000340704540c043c3da0140001315103403040c0010209034520850103a1a01c501c160340b07410340305d48500d03040d0148550118080c80030a0040d403055918420403003003034044412071910840010302e41400c0c210301c200000e071540018850005040301842ca01101c80c100141010008240a5184d45000340803202 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 30278332 1250 30277082 30277103
    0x5030c010806030c0d0c030b01080d1d030309040c261501051b070608010602060603011107030c0f0602040b0702030705030c030606271021030e010309061b020601080d1b 74
    0x260f5410b2242400e58180100851207282c03140c6040309035040380e480141c1d055608080000349900b404280b1041c2d51010303039078401c102e0407407600d04c2c858500302d8040c1e150144070600c18002c1039140c0b4400c0da107000160fa102c000740d01080780c3c04040020303006808820b0251480086c0a4a9a0008842046041c003402c0150303c3c2c60300661000c442c40e02c0100366415a01c1139810009801d074000b0b05140c10391307003107070309843d0255202000d05003610110000450a80420091140800d00c07484000c04058482c100b043c0c0040b00c141c071040b090340c029402451100ca80000c42c0b00440c81c00f00008401884180c01070300300d0344101c80000381c982d500105034038040e810b20200001d44e800b03231441c10002012403142d180050305046030b40002c1c84041d40100000b814034011282d03a5107103103000e01858507038503070344c0d8000b550210001140981040c10040300e6441e122f02800050010920060000701603980c01030020b589807e00c0c151510715102d88000c144004c0d25410100c0c00b020202020f2080d41120110b0f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 30279582 1250 30278332 30278341
    0xf011404180905010501060507140f03040306050405100903030b010e0301060e04080a0c060203070c020411032e120b0a1d0304060e010e0306070c2f040f020c0607030209041505030c0108 81
    0x15200010b0002c28652034040085210b542000c040c20038603024204081c1005601c0124640e071710217010540e03810398000e11003040000c01903006503500510480a840e217980344c016810054845001084000c01c0c1c8501c2800d01d507503803069481e804140210002d00803540340c4000c018a0700000752010740603040009400314554000c0d880303440390341e0380044110f60300e10304800c00404482c154039040b0b1240d400c1003454013808480e50140d90103000a0742c01c007008008003a20103951002c0d0351101d140d42083c07030040003c035000344078a102c80381d501903211082d003031800c0d109580441d00b80b441043c4502e042d580210300d4690000003a542543c000381000380c14005c01d0401600e4601d44203041680c1841031004020029900854182c00036110320400b2100000c45d50905020110036800c95454105030b00424059203003540101910601c40d031801450004e0384100300d800c194046074034101098000580d0006800e2501c124518145100001c2e0780c414205030001c3d80300c14490b080380781001400c10104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 30280832 1250 30279582 30279629
    0x50904091a0705030613090305120702160e0f011505041403070308070f03020f010203130609020607020a0e010f1505030c0d0f02030106020a021206060904080d09060510050f011404 79
    0xc0d0410a1400108242c80d2600008050b0382c4100c0c1d2141c016082c0200307142d084441405074014556141e1141810b04400c507105006410000300048110302c900825211107101515040001c3c0507590000c1e086442c02c1002d190220406034024114a40e0740b1107101840781d4400c0c16602501c0340805000c1d01c038400200003d19007540d0b5040540b0301c000c002105030401c0390005a580807103104e40c081d150041c990000d0305080b40021207050f402011441c01c1e03000054080d0703001a00040c4001c200d5418080c081d0042601c1d0401d9410000b600c512010062150100c1d46171044c0041980311511114012031a00c01080c500001d4000304207800080780c12070601c07085820408100c0705410085480c0c0d80d5684d0b00079550401040140e008a551145d5902003000205900d442940c0140c100f2240b62100d5031003000b1a0301c40041e0f0b01d5083e950310030326400244280640b40c003d110b07070050136030428105401c020b0300c02c40c00100241403289a004801c200c0550300152804c98288401001013040020140c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 30282082 1250 30280832 30280853
    0x302040810020705010b0907081512010507020102070b09030f0403060513050a15060905040804050906010c06051e060603040506071101110d0207060506030a1104020d020408010c0206010512010c05090409 89
    0x505040c056202207418440142c2c0c09005081d006200900c4425606018031184007402d46898001a0307400000504200400b49002c0c0c031070030045d2060651140350350b9224215401a11000d00507500010200280b1006100b019003004034400035503c0d2034282d1200f03981c82d10851200800c01600d541c0015070b11405040716441c0540c100041d1209107040d4503022608030300e28104026050f24121010500c8091881000c0c0f00b6071740541c40a24003400d040c100302e9002c000402450410400c4040301000405501800e40254410b0301c80340d003400300e42c0c0c08101503a140200144e002d10b2040c4200401708000040d9035800c10340f14142448022140c00e0040c0c00342c803c594018900100004101c11031128a030700801800c0c1c0542010000d81e1102e80400d030b2158100707080501511200e104c444107614160303004040d80710300500d00500d4a0b603100201e0342035400d10b890300c1c0b015030070240c01000141002070f9843c2c40440443c0003082000401c60000d40b55024111302240a42d507183e06600030000c00461 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 30283332 1250 30282082 30282089
    0x501050c060a05070912060f1a0109170325060605040915090302030f070c080606030102070b04030e0109050406060201020a0e0603060a03110409081c0c0c020108070503040c051309020103050108070b19030204 91
    0x58003a0b004400341403200140000788004001103107403c40c1409c100c1102d68901c1d1a25005175100c981003850310300840540041c017142e6042e0b500081009100040c504031459005070b801c107140b00a84c040741c0c1400d10448a580d401280a6402c18180c8400500c01240020b1200280c00b03001074810701604040386180076002c0e002c41440e6001402405200c0050741100440d6244000c80c0c2c0e156489505050a0340a4003900404e0204403c0109000074015003030300003c43c07018035201c1889035480340040c059412a5212502517580000d056001a9006103410035440090310003a00e94100030000c143c08602910000c0c02800031010f4505c61a41c1c3e030380011203071640060455895001e0204100c8841c00407850801c2c210f450b00b03003154051401402040140d070380585801002e6070f2200800e46c2c0e0f5600081085800050b840030210701e5994062406405010b040400100c0b5030700352001504036003041c0c006c04007d074021402000917000302c204545101c1d100003070343c1c4180c05c1d07600c0003a0044e000d542c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 30284582 1250 30283332 30283349
    0x210030e0d050403020f100f0813120e040f060b0405041d0105010905100608070509060304060e06040809010e0906280806070503060a0b090a0b16060603080403020306010501050c060a050709 83
    0x7103011039855006014200340ca000f2180354032100b58910401059101c2c40060b50007160342c03105015080d5019044043d40104641c0088079094199528084a10141c82d20140480d43e00114140705092031f1041242c5145104002c1184c44c0c280304024071035005a104a0744140e07160051f840d81d44251a09070f43d291038000f8000e005070f58560341c10303201170f040456160006a010b0080091001e1180490b14050f441d50b840341450312590000f0b00c09035030b100400c1520380139158802d030003150000b00441c51007280500c0d206500d0740705010004011030600b4103070314468505402031150507940c8280311760305034174040d4500c4a00d44401000d5032560180b548012803034003d050410a0194100300110300c101d20442e1030b6062aa210310305802c460080d6040c55400100702e801c14010195440003c00c1448001450454020303010395031030040d00d2541d00101e9040300041010401c50808005603409410242825804c0c07219594a6950b0340800600c140d008136100d802003500580503d100d44094078112 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 30285832 1250 30284582 30284593
    0xb130e09010b0d1101020c010c080d0515031b01031a0a180902060705060105011806081602120d0b03010e01360605090307050d030605010f08040c0f1502010b0109030f0210030e 77
    0x1410300826004c4404e00c000e0160007440c2c50300c603040d0712171860101402c0c4d00c07440060600e44089000001403038003e0042e030142c5481100c0a40650f03040042541c42c01008e03081c59a84201d80d4001030949002050b80c05480c8005c3c050312074141e07101011103007503e1011845c0e01c2201d90600906005d007a100390060f400c840c001a40a0621401050306030590301e0a0300c42c1203045441d45642828441c0380e1054500180303240011401c1d280782c2182c00d5070906800d104648210342200a0146c0c10380c0701d00c18a0b940c00d543c604010031030f810203002e10100a114140200300c03414001c9050410140b140781a00b5214130840d20340d1036020811001140019080307001005203190802c1b40f56a00d500280040e10541304455514100d10b200f03004920640302d040e924540d40030709100065032000d8015008407645094483c1c04a440c4020940d00300c02013100d606034003041440f00c40b0290841d0740b4151044c3c10080c030300c5030610206194150154000350f0644500d803403111400c1303048000b0807140410300110301a9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 30287082 1250 30285832 30285859
    0xf12020717030f0609130602091801080115090c081f0b030c0406110f07180603050a1209080105010503030702120f01050103061e020909070c0201090f060201090b010b130e09010b 78
    0x580e0042c40c414003d00a209110361a00300c200300201c0c0c8225400144800f50800d100c0000d0300035000340842904c054900b000d8003003440c07000354104d1001d0708401400d0399111100741c01c080f8241c4801300103100c0d0b82010096501103080051112100420400c0e2603124204d014003001c114004000040210500c0c60b5180e003031210342007c1e542c1c418400c28000032003c054401d030f0810007207111704981c1c080c00300506d1460314043c0004941408c107904200b00c00c2e030b103150000204005002c612351862107045501d100410180006d04814a0ba4010640036850400148241d40b4000116558590100d520301514440b800203d4980440540c09c0606542813400000800001f074003d0752050604a4204070180d500e407a000e022406003801942c1d000c4c440201080b600f9006265080c01a0300600d00361042503119506407035101d5459100301d0060f135554112400307000d89c0e5400c0a0140a105000c1c5240c100c4000308950300c80e4690140202d01a049070114a03004000d500c02103189002501c1200032000c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 30288332 1250 30287082 30287123
    0x40c0603230906010509070e09060f0406030c08010203041a09070b0715020c010509280204020310081b0a06090803030f090f010c170a0b091b090409060b0301060f05010f120207 77
    0x400e00c5170500890102000c2407189001c3c2100c01c24107180a040425141c1e902403c100d441c0e1030004905401a59810b804030200700d0590381d401c080d01c91000003503640e0410b494040c0f454803e40840c1c0d1a0203c51000380300701800040754110031120248407407500c6041904200d000080300d1080d0303100481c8006241d511810043d00140e02c10140b900546043d40070b0b0000101500c4013004418400c042031040b003d006181c40d42c06560440890341407034201d1520383c1c0046150207213620801150388201c1c81020000d14005840e00c002c0c1015140000507940303404092542c0780000b408492200c0f844e403000640340749040048482d03030041c51000340040005c11b00e003c3d0004c801080a84140d1801d0000030344c0703a507014000e11045040140000c00c041c1da0700c909500c901903819480407a4503104200d41d0420340e847e070060b10101e030701414000a0b001600410542140c185610020918207542d5040205a070002c0c000c0d42c045071079040580040c3c01c0d46405600910031020020306501e41542c11101015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 30289582 1250 30288332 30288343
    0x5091c0c0210080702030a03050a11071b080c010509011d03160e0c0301050906060708130e010e1303080a0c090506040305010501030317010f062a080c1203040c06032309 74
    0x28002c0d5428003051900103422584001d0031030b010005a8010058442c50600c80e912180d480480c1c0d8038006080c0e05c01e00c0c01d20711581e00940e015645c00d01114500d62102c1d104004140040c0a044004c050800038640060010301411180c14144094007411304503035030030218440c00c041c20040591b0440010103148611020860003400c4100b0466800a40456078090459050382d0000749102e0305940c41c0010005a80d111078800c8880c035905102200030303c12a040c40401810140b0000a0150305161003481d240000a09450170607440031440317000319030840d4085030022641d5001041c002507008080d254000d181e80a560400c10004000003485010340c07045040e43e22980d60494128449104011085000e00400c003541c01d01d11001c00401d40140447d00180c840722502158440100c9030400703c221902c2c1003521000c0002035095280d61007031040d0800403d50350034070f904508168603001c03101081801400d0070706568080802c0c0f0a21503a01c14162201c0000e00902103240c0904c08a403a030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 30290832 1250 30289582 30289607
    0xc060c090a21020a0305060916032102030c12030105100206041208060402090306010810140403020606010c060f05100e0601020703200607050a030210050105181501200a021005040f030605091c 84
    0x20b02070400d1040c9ca82c08450300800c11260807000110300c03019100c004903513031100031061350103503c01040070054401c0c00784a5042e40e21607101e00b503903c0390300d450180403084940c80f030450304540052007040002030182110301681c1d0854a071072451544d508001c28000d00c00c8903100c6a041c404c0e4400020744120014000c00600070140060001c8a003c410310310300f600050b02c006001d6000140095400e5101e118102d002d14000c1001061262079200d400f0102c95003583c6500808240344400c1c00240040b0001c0b03508802c007840181469455512070a100f843c00302011600c4408058408807540c0d1841d058441d01d0743c122060325078401103071802943e01c074041b8207007201881c100340c000221440c01d090303940b8205800c002c51407005c3d41c038011403140c01c2d00f52119550511150300b003c0544100c09c00701135001007090700b00811641c0c8244c0100900d4040030034190f810080100300c20b2010540298413801202d62000010500c1d0311a121282d040c00000d078654003c88403413007141c0c1d070960381c0314484100700c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 30292082 1250 30290832 30290851
    0x603050a1106090a090908070209070809010606050f0405060904060b0f0304110d0b06010e03070308040b072006040e0705070f06060e0906060306160c0503030406020c060c090a21020a030506 83
    0x10301d850180600340c0129141d1a61180406504010074140c03504040070203403084100e0f614084070303580010590740042d210000000c000c001008840442403284401810450601b0b0f4107190071070030a640d00f84901e02030903019103000b244850841e00c85402a8000c1d100d20942140c94440090a1342880d03001294180c8440720703020b074000d601c8c1c2041c3c041c04026031703000f5004003425030302d1800560f103960b80d1603255605803007060380010100b031458001d400942460700c8030642e01d03141410941401d0782185014100c141d010740c1800d80a0b40ca000440f02201c1c01c00300c0282842e5030311032090f6924020600c01404024810031010208a015800300003940d849502070400b80d1610b10303000d6581c070f004039000342d01030344140082080724002c103481c918013844910780a41b240e00c0c256100d43c00c6403c00c2d80d01310789564010906140c0500240901c80c1d0040c1d103010304905014541c400114403620910442503080075802c8105190403902c80e00f480100d4001d0142d0702a070f552881c0035903655008442d8400c0b03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 30293332 1250 30292082 30292103
    0x7090b15030709030b130506010e09010b0906030604030c081201060306030309141809010f09080301080601050108070915030b1c17070206070b07050910030501140105040803030708190603050a 84
    0x24a00914001d0341d0064840c1e54600c038145081d590750b0302204401030030b1101c0c041c0c8050260000100f042040e22301030300d8184c1c2d040c5a2424651b03c6c6600f51600501e070103200b980b10300100940c1ea24005042c0e03032b001c0d0b0940f03000c080c2d000e00e90400a00501c03a481d402d80005458000100d259500358001c5030840703100e603840304080d5a60300600c09001c102c00418961090030720003031400b10614069016004100100001031005440b64014100e402c06002110301050101c01007003c69010b0000b14010318003800d18010700c2c42c00050081051844e402018440c4940c0315200d41c00c903210781d20000124601415120700c80040842041c01c402c4803a004980c0400000401c450019400013620005a40500594200452a61501d40035440100b050080050070b0041790b000303695150069000030180d8400203019410104189440220011001d052040c02c04c405c0000502c0081100e0f4001060314003920305840e166801e2103c00360501ea9120501d003011000300c284000894500c515500c41c800f21807 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 30294582 1250 30293332 30293359
    0x1e0109090203070503060d11130504060e0705060d0c09030221010b0312090402160209040b0a05090a0305030a0b01020a05060126010c050301050d06020c03030a0204030201030c020109050d0e1207090b 87
    0x707901c42101c4060004806001103100307030600b40f0482698900c224008021182c034540400d58080d84001c0358503440c2d0310741c400d200c00c0c4080c520440c0c44080824024080361802c060218420744612401c041c2960740d90702000451610072101e0001039903005241145222031480011041c0f581c1c5241e2845551034003001c0499840c0000300c6035403d14200a020b414500003070708100094101594490b91080704207039090045e954030f042541314078414000d021044c18403151340c1080b5000113200c00c102d0760288900f40040781d0400e041d02e61208082d900440e0701100c0a0040b814990f000c0e2005069204040010445007500c119440707446903540750880d2015070018482d42130310b42d04502c02010a03410401070040b0f0610500c09400c0e50f000e0078004d403901c5241ca64192450303200300d642c82c501a902080510840d07034180a0703a00c0c1d204080c402440782e5071b856204c070360b21007416104400601c1b80960000503503850b01182c0b050703e140e40c1380c182d03190156104c51300b00141c94107160f4544207140000301d55 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 30295832 1250 30294582 30294599
    0x6040e07120e0712030207050d03050a021203150607020301090b270705090c0a05040b07050106060906030e0c04020c0a0203031605060105010801082d101d0721020a051e0109 76
    0x94200200031008202c6145041a01c4d6040141d01030250210301900b5404500d603181d90004a071300301d100365581e9a0340c3d103074800024100480d110102101c0281007040c0081402036005495080c1000c0f22820b13903e04103440060700400b800c2000409000445080140b00c1d040d0503014000e03004020a000054440809420f4844031079004059014041d040400c5c800714603076000e40071000f042d0606601d0031342c40d01c1080c261500501c4044a07140c1d1210011310420b58403e4284c1e00400d03c5c0c2c00e00303103d2146003400880d01d8031103e42d1010701542e070200308200c40900801c46090080d4026058940d2040e841c13501e820203c1c42d54500b07540c944030300070000841d035104801c01d504a803400c10140000c55555200c0000307030132091300c1c80f1704030032943c0300d9100050505026861800c40b503e0300c0013540645000076484503034800e81c1c010300c468000d110100100354903d140d00c3c0c02e004408031010f1103c0410301c00540c0305909504100e401520301c0f240500c0d403006200144527842002d0720f0b40a00c242e034983d001d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 30297082 1250 30295832 30295841
    0x10501210902010e060c0703060b0a080a030c03020106050a090509010501170d0c0302030702100314060102160b1b0a0b0106080c031e040311030307020a1e020105030403050708070206040e0712 84
    0xa100021520680200e481503099015a4003144140741103460489900c0000d44d507500301c19240300003600502c50400c00c00c18903200d0b03001442c40664620007568a840740c0d0b1a1500c6440c03d02409001000400108042c800c0d03111802400d030051442c6a526210b1128400400046070281e0566117090004242c811501c090a1a4425030b80004c043d05100341c0030032607107a5081642141584000c1c441c40005944400c552035110400e590b00044800300354000e00702c1c0f00340192060341903401c10241c1b02d03180705105100506884054000070754441070a110141402194815002e10340600f030203401c01c0104429020303040360f1165903007000f0381d120700ca02d600030b03403005030b0b1410503640d010601d201980c03582c4d0101641c820f0007800d00540e1001c0f0310205504546c4200d0f030110050b08036100c40002c00100c040e10174503440080c400060024030030740c00a465481b014101405110000c5604801c0040000490340b540740d014003c2c580b00c80d920300100078040c5040c1c5030390020699103d030103100d06040d0700c107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 30298332 1250 30297082 30297107
    0x1050a06050901030813051503061014040915091a01020d05180915030a050c030f1b06030402030f0304080115150801140102030c060c04031a0c04091104030506070305040b010501 78
    0x1001c0340c3e461951180074542c801c134880345014203d21400992640c8405200842a11070001d030341d524513000b070401c10501c681c0100300050184282c150040c40ca42c0b90280d03004c2ea17180030000251004042608251119603912590385641003d46444c03403004031407140703601744200b80c08403030a05000079025580340c0982417034010060301d941c0807080c56140184407950411241c001c26010709903184042410804194000c0e542ca5110402ca02c2240c1401c1009203420000c0e103000e80a0782120018495440141030388030781c41414080082015903509000d101a030b5a600c90440f41d40340c0e40c0301ea00c54080c018a010161034444504400258421504004820340751150783e040c0d0345a0030150214142c0b0310b0090f24a0443c40140a8030103c00c01c100304050042c02c20f0003c4a4503186140760480c5150700c54400c10500f680c09801340103000b000700050b030f020b447e13403440b02040c089119146c0c2c0c2058090b56001500d140315800038400503c0d050b50080b80100d020300000043e82c2e807a41c00541d5030740301d41d20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 30299582 1250 30298332 30298339
    0x5060d1101030506040f021305010f1407060b01050415080604111c0510050604030606090e070e070503060112021902160501090902090a080102030705130509100b0a030b030d02010b0301050a0605 85
    0x491141541c420b511a1303034030040c0100b0000d10315041a010380201c0c1c000d810400002e101c0d494050003190b8000d00c3c41d61690100c2d1a103844502840031151220b030107800b81c01000c042d16243c2100d0300703a00403001d541c003410102d05503c80b503401a000040611324241e034007074062407500c240c04080d641345c801240c452000305900c40144840400c00c140040c18010715000c4002c800540100c1c8550f10280288000c5004c2c07900801d100c0e01308000001140d0006000520ba540110b404108004410382c000c0c1e807210035410070644a592314001030700c21049448000c240b280c80020019548480f042403a4000d420b55821035a00c900c01c140e048030030700603a00501340841d400b80001c1025040380c0c0c000f82003207400a0600040c1d035a80c5e0200301c0c203a030404c1e40d0500104030003140a0b11001c60030035402c0010b00c0d049a1800090508107040c030340c021854050b030f40c1000380000d5074081c000e0283d00b11108583c070203001c03185251034141d00207009040f800301682c4607508201c0810407030589070283ca0241c85005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 30300832 1250 30299582 30299603
    0x608040b0f060103090213060503060f0f0103020603071205011212080108121318051b030f07030c020a0b010e092515020f01020313020a0501020d140306030c030f0106080105060d 78
    0x2011800703090100a028604150315514890300584440b80c07081c1d4880d4416801082a505140805007400c9005194000c883c50f40740c100114003052000d0380d411a034043d1942c0795241c44850086441343c088065a0800504200c000200742075003104207140103018030458102e2422200044913600c4c003c2c13251000d036a2103d08000c0784401c595000340020240506003811107682caa212003446034903034200c140c1480e41c0e0b20170807800d140050941d40c0c100c00d035211564950302d00081c019010700e101030003d00030075a0f20042104014000c12040c0e0400ea08005000d606694a0f0303030400b9030640c101d0340002e0601a6180462120b010b101400344540c440c0084035804900b040d011041610700d0308800011440f450108400492080c401940500c50f132841e860035140a600500c401c0603501e50000d0304650000500c9a2816840b41681e00030015400440d65291921000a403501d4078980b134082d45801901e00070103c8a42c1548104215100301001744200d9407100d041110020070010040d1101d0140c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 30302082 1250 30300832 30300841
    0x7020915030a0b0114100c170a03090b09060402010e010306060206011415040909030207050607020f0111010b0a060c02040e010c0203070303150b0403080a0306270908070203060c03100608040b 84
    0x1100c18011400d02500311400c0c01c10545442549000a80c82141c000010554170843d03414000c0c1c0c41c6104e420507003003200d04038440703980f180050421a0f11035014408040342113821107119410003081d01d038000030019114100745c407a01c0c2d00c428059408a000c41c0070302c900341d5801c1d4040d000d060104c84481c3c000d800310340e29003180991108403136201d603503003e10340b450708684000d01d107030181001d04495000002c03405100d01d8080d240c030380c881d0056071040740c3c01d0100700016651a0310501e01d0702801e18104805445400243c4d01518154030039640c03080042c20007007003c03903001e0120f5207014021201401080024121103089903050080d103170041e042045900c2c0880d0003600281e0b00f001c9019203407840a50749041c00402500140c00440703a02100046801c03c46070b1500852014001040d17041c0e0103c6145004032860a00800100d6840340d00c42845030107020521040d203203000d4014040d1042480e00ca02c480c41d650340201c1c0c004101011094022500318032521080b4403c1c2e0380820500f506d43c56 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 30303332 1250 30302082 30302101
    0xe0a050a05090a090c0e010e0108011a010c030e0301021903050f0c07031b020301050103030819050601021b030102040b03070305040212030901080a0b12100e07121703060a0f03050604020411070209 86
    0x100905100201303842d0040c0c07070005202d50748054000e01e1040b000c1201541450341218901c0c2c0103a0101203180e04200c00000000c101e0306110030190000d08017000904020702c2e098410505040d0b039564154030100c1c241c03074005101d0811039490542c0e6079003000740340d580e94103180350420155800c2a42000030b0004c44d00090103958103410b1340340540c20401c1d40c0401a4002030075100260000c03400620f41c58144101e10b80c40d200240ea100b0561241803046150400000355902c900401c1056242c49c15081d034402c6403030079030448018052030101c80d96a49090440507025000a907800c038051210314680c041055004020b4601c00707a0b0513980c007409a1294542c0e03102070007410115a60200e148400400d00c0716007000b0b40745940a6001010a070841264a030a045c10080d501007116440301d151082c0009420900c8003d4000c0c081901c207803070391640000b02e00030485507000401402410a000b1081c03000005130f2511651084900b481149127442110400d07000c1d580c002034000b0080004944240e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 30304582 1250 30303332 30303349
    0x1060509060408070909060b040b030a0201080714160210020616050318030705012c030f0705010204122001050f070f15020d050114010504030201090b250803070e0a050a05 75
    0x3000205564242038072444601e08020303142d813120520350340c0d0344081740800105005506000704200e80c100003640e500c00c0401c2c1c0700c6056000003410413010500050030240204003401107441c801d041d0a895100b074940000b000c001c29982a0310910b000b00e08845054030005809100c1d034452049400302d1030f4031450940b40c076000580212800503000f000c211b0000000c00250820900801c0040b4401405c002c0215860340462000d100300003200720003088910002086801034880c01c2e0740650794403810700b0802e0081c0202e41019020b290515110814040b5112a800b605044640f0069003407540070300546aa1050440f0b8610940040c040c00740410204403410410394007500034661020b10340c494030000c0380d0102c102a0500d0342c3d1200140420210000d10104000c02130814034903007130464001920000c254404d101c0110000603040034080848103265032003070120078510408940758509a1496081103441c03a001030100d18011200d4903284800800b26a4060580007040f410f03d4103120243c0f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 30305832 1250 30304582 30304597
    0x705010204090203070206060a0f060c1415011512050f070c030216120b0105060301060804150b06040902041e050a0b0a0201060b0c1f09030815030c130f110f03010605 73
    0x9550a01c000503107081280000c511840d0725034041c05192034240108507181802c1d80101c40407510303021061200702d80040c4aa00d46036000425480103e02c0400c101e403400501c90815046400040c00000b40d910f108500200501c04584613160180c45140c3c0c4c1004a5804440c00b40094108002083c5c0e214000e12640100c14003d02c1030307036000e15944103500d48001e01a4010660340540c0844401440440d00c149405090200c54091642d490200020807021002e00060300e200000580d18101100c00d03880007601c11000340026880d42d070b031000114029005031041c11500419014840c2c0f101550028640645200034802003401f030400c040c1d030200c0d40085001409540d6a101c1c0828480307030302720103400305841c49402003091900307108c24050b0740380200c91040c891038140680c0c400002d81041c8642d07480101014961580e00e010070000e0710f0051002c0c006a040210015890747c00707406604a5116a00d41c284e09015011421130586098420b09000340312800041c001131101c1c511850003043c04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 30307082 1250 30305832 30305843
    0xc03080702030c070e0114030a0209010605030903070f0807020103050a140c180301020c01091103060f160e040e0f060c0403022b0c080a0302073303021903091e03050d0207 75
    0x1803220f0150582d2070a10305800c00440074004000401022075036010406c0c2c0e40d80258003a040e032590aa010803000c80d410301444040c000e0110000c0c02d100c1040080d54909900709414080c1c421040c180a480c550051505a00190416000130040c000c60701a02001d40f6020303c0140e0250b449a2405501d41c001da0204144944050644680360740d0034000740c88050304250000413409581e24100c140301750b4400c6002d01a41081c2e0030002c0d00a00c02c5111644584042040d20100d0038030321003203942c5070400d201594400d24100100303c900c0d00000344c903808080490104d901d240c8561482001601030b40c40020342c40804412007880d4440860071030b031245002000344911200f030a5076000d1b1a0141d98001301c2056000c000400241a070400420b4010402200c041e4181600092410202d4800040e028802020b40040501640c403c0d0f04440b0303085108021040c00b28019070340180a0005d41500f07651011b2070094038000070300001d4880c1c40013039064a540c4d01d405900404803000e5000100c09484 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 30308332 1250 30307082 30307087
    0x305070207080a05100c03050906010303050a05040510030f06060503090a020111010b1002031c06140f030709051008010605040203070f1107150f20190f06020a0908120a0c0308070203 80
    0x10150020040510064444c4015080007091000b407a41100d408210354420542001c00340701c140540846d005040d80e405183c40c81c0c3c0e03055048800d41d100e01c00d5600c030640103002c9a861801a07680341c4d114a0810444903014030501d90340b6002107541e80000d8074505015080b22140d040158020750714000c2d1a401540081002d185090000f003901c00e4a01040c40980c00004090445503600344081d100c18101c10340820450703091035408540700c0542010240554914000800155410030100008121070742c41409103107000f100c040640d440c0c51140354400c1d801c003c00401c0c0c82c6810700a0301d100d174010740d880c043c004001a0302280c200c040030507c0389039130091a50104400360000e11411200e0038a80300c001503248540c2004011340d120528080030540c844608a05a032400310fa00c000c1d03600315104c105186071040c1000302213000c124100030180c0e07100003059030ba003036040f01c80d00013211030203c1544c1c440c0864001c00b0b24588a040d040c200015221000c800001e03005d40340d50f0750480b030310744116070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 30309582 1250 30308332 30308339
    0xc061b15070302090a0f03030801270903030f0c050f030604050c0f03040b071d1807020c0303190207050a1d0703110d06050f0109060503010e04050c15030105130b01020d0305070207 79
    0x240e000540350300300000e80000720310820b405c0c4020140300622031011034a1020341355032002002c524060240345001c030707209a01e44990100c950101030700c04a480303004220070603483c50090020000b440214040d00e080007441c107013403805001a0340a00701565001895903640008001c010003000b400214483d00c1403100210071042d1501075407245204101e880000c1c00c10180181030840141241415003600520280307040d00c0e111903100e42811640890403042e00c49040503030030310301a51041505440081109040845140070403403440b87e40340c013510705180d1500280407013a24140106506a9040880840009108290309601603e5498002081403240902c0d000750b51040d0307400d4244030b441c0e6030284100d18200c84016a9168242001521545861406132042c001441511640301c2003400050030701600b400550385c5c05030f0050a42401644c04c3c4c4803d4072980080c080c2e14025018200050010790144c4034009020304141c00425804000d48800c8003e448002c1141045025110000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 30310832 1250 30309582 30309613
    0x61f14030319022404020a090612020409060e190b01080a030c08030a02090406090903090b031e1803040803040801060602010c0503060603040201090806070c05060a0c0e0d050111030c0a0e030c061b 86
    0x1c0c60303844c0680f04c0111400d140c0100f020504817604031411191410104100c10b00b4100000c2c028261705440100c0d15840b5414003130300401c0b17428400398075400395220042c4541254a40c2221440c82114000034a90329210200e0369564060030040101d142d400180b40890a69030155520600d560009843e00c0c451a000c01c05a6805900c08080700e41c40b105203a04068100000801602452030302c00d0651806074840c150b5140701d81450540101032002081c546c40100341440e1303055040ea02100c2d61680c5e1241d001c1d1303480e07016114000c40f551904401182c010300c1070240741805219552028195124401040000d41c4050300807410700102401c000f503d0350061210520650341c903141d1024405940c182241818801000c2c014000c0c60f080c19000031076004071000540030b030709039400c0c00001ca461500c1401000c161070b20400c003001c04000c110042070010010051280c0d0f0f5070360308034030390059020706945503480c000360f43d404042845030703500301350021a80f8000ea00000c01110051110720158 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 30312082 1250 30310832 30310873
    0x30c0c0703030c14120313020103060e1510050405030604060b03011e020c070e101505160c050117040c0510030f0207080904150609120606030203061f1403031902 71
    0x1140440c60601141c001e001c1302204055040310040060211310070309405c0080288002410616144402080c440559110761300002c05000c2f660320041d16400c1c11070740541000c1148031032034441c10580d44040070091050064400301d400180080c00261100e0b52040042c25030906440e8056581e5046940c42c0c941110354103501401c0504016540d52043d28840d0614016802c000315242c41c40003804082c000c0441050111b50a81080c0501c030105a40f0458041c46418030000300540c0301d14205007442103a14005049640c242c03542c03030402d0b960400f03011501d0b600302c40284c4880e0300881d041220f8200700d07010b45012004c6160000c0d41c05a0a08603d04a0700120004d9440769004103071108036050600c181c4180205465028a15601e40980206034403442d00075a0380c103454003140b103410003040340c01900256900901b95039545c501040044c0c40513240c0c0d080e03128018400c003000116100541c0e03010124420140203180307041c0310642d250280d9102c0e04560b5086100c1c280c04616440011500d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 30313332 1250 30312082 30312089
    0x60f06030a0504030801060309050705090702010908030915060d020d060903051c0209090106030603021e0a120605090d0306061407020307170604120e0d1e020402040801091a0615030c0c07 82
    0x42e05041c541001040000142c20403030526260a101002183d070020301c00d2308544080f501400940e442460483c050000d8090040214001100b0b01035008004503040c3d00d0780102e52500c2655a8031082085001e20110030060741112080c1800340110b0900d8010250715400303401c3c294070307140ca40421840303d5110186203658507035000c5070090ba24038102c0c00341030043c49540b5041c4000383c1140c00080303079816410401d0b800c3d2001c1c0c00c2c10505c69182c500080e40245411480b88060307081500305040600070440382c2807050302502c0d049a0005010f07110703034016141d265480031403c02e0030b0380341e0500a43c0204170903070749841401d00002d41c0c00c030b11010041c06011000050316040c20329261034441400161850400c5c0035001022198030384400800000841d003285180e2160f00310750264092609003260302070342050000070041821101500003a191034410a0a0380c40b0407030b44000e040e0003003401e88020360b10004040145a10700c842ca405150010702c0681350b1441d004014415529042c081d90 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 30314582 1250 30313332 30313351
    0x40f05070e07020a0507080c03150712020406110d0c0c0b070302030903030301260d080601030507050d05010602030a230301060c030909090b01030308010605120604020f071b05030609030a0203090108060f0603 91
    0x1400003017103c1030100f04010a035460040c44d000e4080d000182c0c6800711880e000803841d041c0c000280c9902d03c1940d460316203002d82c180c01c542c0d075512014010031064000d401300140d445011030700c1404030f2003003d07540a07940e0000494141c060800a142c82c484c0d010500581c01c611092080061540d41440258002c200d114480c1b0030341036074000c04402401c100b01042441c2d4001400c00d6041a4000b08669070050007460000345954070790354292654050a00b01c0703c45140303008000300d0070a0b0000002d010700300700781e207501540c0c02440320301e950081006151018050030900c01005000d00502242260500c40c5c10400302103a119001d8804858900209039180100c01004200340354000c06980d002d0402e82c0750003440c0454052503509200c0006d400076014560018018400b5402c410a1381c0046600c80d452420301c1000008400e8505401d0284c3d0b4844d00038000455003800c000421100c000905801450030442040300649046174024443d0ba084085040c804c0d05680c2c540c00110320407030610 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 30315832 1250 30314582 30314593
    0xd08131104050601090b0c0d0212030705040e040f050109031d0406030503070b040204020f0c06060f010305060f0d140d09090c020105070f0e040204120303020c010b12031215090115031b08040f05070e0702 89
    0x48c0b80003890a18241c4003000d0410042090011440c1d01034200c40940300c08a5000b0850313211031504613021958804060710f19481d10148030308159200d84803140c2d0309032240d9041ca45503600d20070070007180c80d00d100c010310503403081000d407000842c40e03800180e110780010401420303d04002036511259001c180e0649540d0026010441546002c00c0030f00342c20300302842c0400040c500600410408a0b000b21610702c102210350b20707041000030710111215003078010000e4071440021044064048640c601481c00118141109111304610500c14a407041400b60350303014200c0c5011509480c1c030b044449211350815000c00001c2601000c8a44031500d1910941d801a40c0d5401c0c840400d08407a1040711070361080c164581c44010581e8000117940c4103072402c3c10346106a0316a0030900c501c0c01d61504031075800a0340c0100000ea42c00846000403600000ca49060005420501d48108075000c0d146180d804500303498042804a055240e416010341d00c550300302c4040ca91a401480768181c8202e640c0401a07205 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 30317082 1250 30315832 30315853
    0x20d03180507062307020604060318060e0d120e1c03020d0204061d0d0302030a050a05040302040905060906010e01050a03031d03060109060510020105040812070212040303020d08131104050601090b0c 87
    0x3c512100c0310b0880c4190605042c0185c07903000442500c00c0c0c1c480c01c0201074540c00b6207618841c0c0303017030f001040c1507004001300800b840b4800d146480b108140c803640003051209000c03031122051805032040d0842600003509496001200021040d505940134404040e8203108425400000d0320003072000e40301da170b12802c3c40070f245410350720b212059440d946030061070300d03d05840c002600002600e2410415040c140e45603140c14000b1503540c0501c0d48040d51107814082c021040c01402b00d05540100521019940e1a030b0300d0302c00310a60795500780f0030207800c2401c00750100b010922407030945c80c000050099440f80420104002480c000c02a0488003542c1d5035100e040180d454440084503049850f0300080c0003500c1c25031110308560052404151201c080000003944061003400342d925032864200255031156102d0030f000707654100e1440307031030701007144d480229070302c040d100b509458050780c06a01c91141c1c080481c01d02010b4130010300f02905014a181d404140c0456003005849045690030007480744600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 30318332 1250 30317082 30317117
    0xc09030b0915071107061b081204060b06071101120204031a06040b0a050607060b03010216030e01021e0d0c110d0f02040609060b12070c0609050102180a06020d0318050706 75
    0x4016180c0e1081c00740640c801e0200c0130001c82c1e41c038103e8116050114592215081194010003800c0c4001d00c040b80001b1010024004600b5541c01039000e084200a511102010712040c0d20600c240549a402150800c1080750310070740040c00d0284a240c00981401d59030307550500024440c0720080c02a04064003003060a00306480b46004802c01150003c1610746014040703280c1c0c0c450203030b000e40080d40b43c00300d12165460075011203c2c0c20643c2e403840d1141c0b101c94140100030382c00c0f0f025220b005018400e00505035a142000350b010100c0032101a114203890102c0c00d07500110041e0741160b01c0b04218945003815600c4200510403135010780407080d10310440b1301c10401196015040540098a000d80900002e680c080584442d105025070000b15500c0b0741da07080d1600142c1c3c880047c40181441c01d020108007043d009807402600700800d24600031000c100b04044240700d17005160043e40b01643c41c0d03429a10a403c01c21000d0b030b0f500c0c285040c901d01d5423241030401e4034540040000c20381c29001c04a4014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 30319582 1250 30318332 30318373
    0x20a021e150f1c090503040303020307031206060822020a060f1214060607050c0415031b180b180702010204171204050409020301021606050a060b090f01030c09030b09 73
    0x5640714111490701d04030151101150054440038020602c00c08008040395030954000710101c1d030088126a115a50703403900075a80d43c0030090440000782d0544140000100d54010802030b11132a8940c803405558203000103440c034207010340014840e0440741e000380151f191039130040054001581c0e0801c1035056a00060680780d20000c2c18800680f41c03540880b86885201c0406820003411034490366561042d04083e40f070a8240321145510920748603820345440c1680c40c0c40000c4921034030100e00784118120608168140601c540316004050840c000c0000003c1e40c049641840000d1801d00140300c03520042144520480c2c0e8200540c0d40020144115269130800d2803034000b2a00051540913009a40c411050090b881203502a540341d0329a40304556081d01aa24440305080207034030040450b0828001800301610190405864810041b900f103140000b200c01d076800162815134049188170044004100d81130382d40040140d28000480081c08102d01c0301e0207234080f5401011280112203d042c0300e80e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 30320832 1250 30319582 30319609
    0x81501020f0606061309050a0903030b010f0806060903011e091e080405150d0507030902100c0201080c1b061801060b070f0b0702010e010e061b09030a080a020a021e 72
    0x194070150924110400c00030300c0c294050002d0322031a03100c2084201000c06144150800403080e0300b041d04000f22000e0384d92080300b00c2c9020380c5c0c00784800ea507800015a8a191403143c0d90000601c1f410021303603182400741c01800c001c18041c0001401c10348548245032000d05501c120102c41e611090b00c0014480c06007001512401c00111100150106503141c1c0c46034811481202e02400400d2410312100e42000103846182812440c00e0002d403801c140c0082c001d0503040c0c401c84c030600704180c2a068181c071611032125070503030684902007581c80c0c440d810f0303509821540c0458000d1144800320740124405003c036074020740c0412841400c020005a034182034644982050780740c1542400305070046079661034015600d40c0c01c200340c4480c5d0388400740124092309810503499419820038401d4012a0070000d02e69204111b01d014986409000300309500340c5210700217190342d0550192203401d0100300604020074440560340111080c213919980404d025251001100b01d005146200c40f00c0e080c20300360f0a50080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 30322082 1250 30320832 30320837
    0x50402040506030109090317090f010c140f0c030405030a030c170f0708070606030b0106170a0507020a14010b0a030c05010806010c021011120301030605010501021006030b0103030309020619081501 86
    0x400e4206804a512030005200325502c542e1201d02003c289400741043c03813821005003202c22164030b8900031056440d407070010160040e40c6045842d11a0510903031022010301e64800110b45003182400c074211745034010440d104020f000400000529540030008582d4903032180d16449511802d5003000459040320107181e40000300100814050b40380c501040350103c6500204040d101e007241d080c0100104840e41008001e80403007000030a015030071607200c42225201c0041341d905691010055000d6a10a59541f40541d0101288900041c50b01181c01c0000c00c0d14400010b10076600f4001401200081c4d000341c1d6800461401030086592142e00a030b444071082c03d00110290141d404070790b4100420f0a0102009140742003040041c00522065589502e565441c40d120b50710f90a01000400c02072180d0b07130151040c8441404c0c1d0315140c1c0160700440e80c1181d88404036a2858500350040e0508400032a800841000f5102614401c5081d64040c2c0d000c0e0303035940e42c05182c440a21401e401c05001d28a05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 30323332 1250 30322082 30322087
    0xb071505100807080706090b07050a050f100e010b030a0b0403170c04060f02010b21071d0106020c030703260f0706050103020103050703020f040504020a0c0b07020a03170f0a0905031e0d0501050402 86
    0x2485400445550454908c8181540d50700c45030708003141083c519510050440c040c9491200407101d0005003e160210781c001c08008440000311310a00700e071040d2580980503000418082d000c51400f06442e50301c9070183c00e01c09142c001c8a6204609000d0488041209440210f0b0601000e0f034842c600d006100c410f80020858100c1175000500d000c10703446611150040361900a0302001c0c001d0169800401211414800341000100307005107000c0f00f4081c1e900144201843e0b001c0a207000a40007088940024402101d0340c3c07086c01c0301c100001d802c817010150300400c209600340e4000b140c000b007029602600c000034155040d0b05c00142520000341020040500520002c004d00007080100c4003100c10480300144e98403a0504159006400840080d20303424444003004001600800c5898032944659510520b04074600300307a0b000200169401ea400740e03080300004070350b03802e15849048010b0241e803c0b41c0c206950301030740e02d020f00c100c4000d0480280c40070505d8020304140380601405810102d4043d030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 30324582 1250 30323332 30323339
    0x3030f0203070518040605030d080402030f070303050f09011803030c05010b03060106050417070308160b130305030103031b080a050901020c031b0915040903030209030c090708010b0715051008070807 87
    0x8110780a0f11074040107005004d010080c581e40c80d603102070300400300036007924624031110401916142040750f06030301034055400011200300012540d94280c80e85516460308060344a00140100e400001d005818030143c005041e5802c0f80e03420075803005502c260780300c00c1c0346810707441e02c00c0c00d486005a1850091788060b0050000c0c540000c1a10207585841d040c01c035000c8203402c40c5a18102d110743c0050820000051001c1e28042920703420f400c03841c000d2a090595440f18a5403002444003010082c0007d801840107100007882201518418031600f22003518200346522115001c0e4002c0e00083d010420004d150359203540c0620600f0403045044000c0c0c0340c18040c56a685100b4115850158424904040028681c9040340c2c40103044000113030082184140916019000b0761182040d81d11a100d80300c401c50003031030840c088501c0b41c0740c26643d54030035901e06a20340080c0d8010b0881241d003101c42c103140c1c0e454050544220f41c4103030101c089081300c03940b81045450508919803c0507006400c90300061 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 30325832 1250 30324582 30324587
    0x6211a0408030601030c050d020d020408070602210d020c0d020304080d0504080307060b19080601050a050405060d02131e06030c080313050603060a09020a020c09060f0f0d03020123010303030f020307 87
    0x10b0380d01c54401e0030007040e03103000d2005c1115603100b580c52046c0528030224810400d0f1965a01810a840c11241191590341e1245002e981d82e0903850817468030098044010003030900c01c023001d020119007502c000760400320005801c41c00d01f5101e0139103800681c0045070801034000100408080e100190a0581c609810f00da041030b1070340b10321000941081e448010f0815a501c0f540b400c101c0078200e0111081e009a101d0031540c0d260407013846203034401c01c13118a0118152800388500ca0148000806400510b58180e01307012051840b4800040110350303030f0420707003900c428004040d48004e007801d000003995411860203010400e45600004400d0b80180104222800c6a04004050b1841220035a88964440001400d80711040c2c0001c140140040b500302d1503150006800103048000301c030310221a41e140020f00112030001c4c41e50507449049601e10032503d050418424000754000d2001049079108a20600011304184060701c81d0041d40200420925602d8410b148041036060015895400c281d83d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 30327082 1250 30325832 30325837
    0x903030210020c0a0803010303030c1812030804050c0d0b04020411070305030a0902061c0209010e010201020a0e011d1002061617040b0604060e100603111201060c0606211a0408 77
    0x4034007900d90002d28500c0307003c03003000707000c4ca0244d00980180e6250b0b103d1600030094800f4114a40204204a40c0ca441c030b1003019204100ba5103249031881034900e41c5860480d000304001d082a00d49000d81021a44607032034688103901d6460060346400401e05003441071104644c00241a110300740014031004001035801411a90844240b2402113524902c500009145101e103d0200c6a40380c1440100c0080740342540292005000036214020b40c0301d1301d0001603081c0d01c10701d10b0140004e86e44058014441d8056102601c1344800c220b40e40018900500108204070340701104c00003d68441c01c200801100d1204051880a0607071806980c00000888801000760010380000c0c914081180004c20503140d0383c0c015002091803d45420040c10917580d01c40540c21103000d901e000a003800305c08400040e41c00100c0c1c00d01a060b50181d1103a80ca0300d0021035460b4030170711003140c01035104c500025000c40d46001c034034074000f1302c0f00a0402c039140d10328002c590004100400c410b000000010000800d480740e05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 30328332 1250 30327082 30327103
    0x21207120b070203090303070b0601030b0f010f030c03020c01020703050c070b0f04090c02030d050f01080c03010204140d0f080c060708160c03030b0a030b091c020f1902010302070501090303050f01050109030302 92
    0x1503100c0030b40340c1450903811030140c1c0b5a415014480450024240b2042c03a4420380a40380a0f01c0800030242c103501440450009100103a01042e409204c011407103100358010b01040c261441d00604102400e1541c9080e6030001c0b400707800003000404d0310040c030074051041170000c002a5910615000010a40c4c968600407031040d03401180d0340b00e4200010754001c0c0200c0381904081042080b640c03820183c1e402d501503003800361401520581c020f11040b070805208a6064940c0e5155105a28401500b00b05142800b118100c2c3c02e0201c00900c8800501103502420f148800303107020340054a031550000f070010b44002c0181c01c081c00070f10b900c00c0d11160884820100f01d80c1501d40481c090590401249500360668801000205004c082020000700482c10300c0702101085030b0312801d0708110344100e0341d03010b28204604c09904844442c8a440d001044e001c01180e1041c1805802e1001c542c94082c21640c1c40b9901303070042503c900c10810b08601c8510010301501d0242855000c0e0750440d20000c0d5242950207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 30329582 1250 30328332 30328343
    0xb06090412031104030b090d02070b0c1c02030702060a0509150403020f090c090d0c05040b010215010e0a06031202010c110d05070807170f18010912030c1401051302120712 75
    0x3051018443e0590440e030145801c8a034000290030513410a0380d0700c00c28103030310b076006015200001c80d00540309000c94903075440d070f078000f000c02101840e401c40030800c3c403460030320035403204216143c0184c031080701500591045460307164403460750b03005214120108459504104000300414001a960094080b0f00d200043d00c2e954880c0e40c400410000900c21703960215802003000750021b00b003104000e03080081e60310580e4184104040d00005a03030b11020840ca000240c000381005003c070f80001070300f01d907010440900c00320b000b603901d46900a004c0f42c0320490b4001030351108d039000c181d00d41019280d4800074031040280504080c0302d02c000e04a020303030080280803400005112051085015048045004c1148000d5030b420032480b4940303907a401080030044601168090041e19030141c050182250f00c841c1c2c900b80442c42a95003220200c0002074115100741d40d00d440c44a500f003007442464030480003010701040e1408540104201104072114030205980301040500094840d0f0582c013444a6002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 30330832 1250 30329582 30329591
    0x10608090606090103060b0f03010f02040302030c0405040c030201261608070f0806060702010903021003050402090f0c03010e13060608030a090803190f0203070609030c0b0705090f0f190b0301030b0609041203 91
    0x1f5400201d0f502c0c16100441d515600b40f8002c8050003840e0350040086920131021201070000180501c016900110380240504800040400165000d425a00340061903c265800c2941c030402c9044170401e400da070301c480c41e200c401c101d244440c1e4010b00f502d030f04100c240c10300b0740c10746142d00c078010800000101340724040e96020a824085901400d0a14043d60b4020003030725840d42481e200400500040300d060780724480c14000b10350f9801030014124083c83c00c1800c12461a800c0411b21030854001811146c003d14691801d800402d1452003400c010704061406559142c40251004140b1501504050035130b4008200c01702075200c00c2c1801075a01d0000d42840907000c820145c6c16402d5000b6050041c002604003a100c20816900c0b66012080701d00c6854a2007543d12070082c21174460040500381c9030840c11003200001103180c044c4041603030342d2006024200503032030150801d00600d019401102e48010120043c000c0088408907607900c20410b03030b001c0035540740c60384800300c910031212074100c1415610b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 30332082 1250 30330832 30330851
    0x120402041815150b0705010e0c06070b06040c051207030e0f01060e0402090604061a0406120504030503040b0c040f0b0c06131a091204031406010803040501090302040e07080d0801060809060609010306 87
    0x43c4103800b8000c100f107031070090f11041c8030b0903c03a000c2c02840c4503010a80c0100c450401c203d2800c2002d55240d180c11900321040c0b41c1d610001d210091150280b034005120f0140aa485414452a4003912800540e0380110b8070300740811459251034905001100181d0500d841801107103a1f0504544d030080d0101d5101c807007a183c80010400500b2590485d81800040c0c10804090035050401801110029a1a101c4d00303010503440c0001caa0095034010005030b020004500455902041c494100d46c0418942d41343c00d03603405694041c04020390011000e00340210b110444c6800a12035641d0200d4040300601c03041d20181d8402d50512440d05640305910715000c041049130340d0401a07001749101d0f0200032903a5a441c0c3c1410703581d054001490382410b11644c070000c00c504002105540840308185c50f040d1160781141d0800c0041c110241641c26148150744000910342c2040081c09690580e1381c03204501541071040062849070018400c1a903540140244901c50300c4460b542811a0f0304800002007071840f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 30333332 1250 30332082 30332111
    0x30323032a09190e010608010303050901050a0314010f06090504090c030308090705030d08062409010c0305070209010902070b09010c080c0711030d090f0501020105100603020a02070902120402041815 87
    0x15004070b454024800303024003d40060140341c0c0300c09807241c19001c426243c0e6074032400c8501600074040140000c1c0e05101c10a074075402030700907084010490901052a55031590a03500c082000d0780940c00a122100c1d081141c190001800710281c10180c40600000c0756079104c0602024a80c8001010040c0280015003a441d05000c13040c081c01000381640c5100d03143c0d0200401500066411341d07c0341c0350a28491900005d420740d440e644503011a241410162907070b00640d80c0201c000815400d102040016100599415403454080d000e24800181c0b18042810401c0383c2d404001d240412503031500070b0280c000c03a004446150f015192801c11683c4d440b16240554001c2080700089030103204114a80d89681d4010314203e00b9182401c01d000c07034140d55080120709861050300c291020300d1981c2c1d01804054400d8004002c10503150041f6410b06907501050400c903071000b040d151400052606010442c50180110710206164541141c4010f045444d03a80591417290706001600d81d481d004038604c01e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 30334582 1250 30333332 30333337
    0x109110c2508010204080615030c01020a08130b030f251407060b030a060b09150f10110601030303020901030501090b060910120f02070221120f09040204030323032a 72
    0xa42c1c00082d074541d80d81340003003581c1d00d0003a1034259014101c00301c040018200052034810703d4205a0007003484c009540c58440301603000c2a030402c44003030700030000305550701140000d41c0558101e91a1000a107003080440300030390083c1d4480d07500e40040c000000390107a40003515005060030352030043e98030035071442c019000317101c4150069003601502e40441e0900003694050000500161000d1200d644c07a0380c1e070111440c4403080440e41c00036002110b2107440c103041050b5511250203041c04031240f10305418041c0b07811001d900840c0001d400140034000c659050084a00503d8184003c2c4143c4480900040881c00340c14040e0707004098252480c1481c0348202d514a500162124007042001400340400001e98010b540c00e9001300021048074082a001500100381214841c1c06011030f004c94420740e22450b40102340380009494280b008003c59601c501c014401140b19844080104103008440504840050001c615036401802088020861040300352010641e40003e01035031010546003d6150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 30335832 1250 30334582 30334589
    0xa02070204090807060f0203090d0e1201050906070215010e0703020c0a061d1207020603060d03020109080d0606180819050709050a0606021005040206040611031608030109110c25 78
    0x90b051060202c00e000850004140b00c0c2c2c065041032004076414034030301c0700b0380c407080c1c0d040103c0e540000d4400031824402c0c50030080c000c80050100305811f4400340094291113040d07032400010b4102c0e400344402c041d010070480120f04000046200150302d400c030720400c2c210000f01010141074000580301f6000005000f40004564001e00030030514817406180080d400c0310182014040c420030140c03405104480c0305130383d50698000d0801d03185039103503800d0020701c02e8210411800e540d01c1c0c124400c005040c480241024113411b00000a01510b05100104941d110484d09840c01620030028042084080745c08001b4071144100c01100704018035005142c4500d035404030030350502d0310060004110b1141c1040d8202d9859508031115410b0880c1103c0440b842034078000c2d44101c04202c10082c0ca801488180d09540c14001030b00c0c10680c0e11505482c4540314183d044030202000801440641034502c913070441c418010700080d041941c0ca0f00000c0c0c0c1c0303031309890305070405200700700303d00d1100c078064000c00b8081c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 30337082 1250 30335832 30335839
    0x10311010c0516080304060e04050c180d080d1a04090f020103230901090c05100801050d0204090210030b0406060207080a0b0603030c0304090906050708090d0c030e03030406020a0c0510020706080a020702 89
    0x150f9540b00c15042d265000390081c040011405103da0395141792a02819004a00c0d102d019482c1c40c44040b001050600060066904150b28440c5040426400405070418111039040070800c007584880c1d03251042600d907901e030310a0380303018021070108100c140700200c030707560a0074006417004a12401207110351102c280320000100c46401c210709014190009031100d88210710144030f464a480405c020344c40c1191381c3c0b03400038900754010012840c0c240c5a11012600240000403200c6098000c101000115041a07020940b99952040b85007814415040100300f82c0c406042c0990401011039180c2540ca480500309451580c00302d031050f60f090013260143d100f20340403a503443c1d50720000e81d40902018607095800c0d07440e107000281a03500554803948100d00395000b0380b00c2c80540c020141e4013040342c150300350f0070010b00b000b4202846d14100010005440160001d2901030040c3c90820880e484a41003d80250034000c02d80c50380716000200c004c15514103040c24001c680e24840114024060000060361 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 30338332 1250 30337082 30337123
    0x40f030305070221030d180b0a02070b1501020c0603091903020f0d030204030807020103050403020c06030108031314061b10020703030b090702150a0b01030f02030103061d06010311010c05 82
    0x2019089001015814030070341d041250310070380c1c1422150042034181c203507903217800030007802c0391000c0c440d070125a01100c495102408400035840d000b1054a040395000b811550000b00c12051100e100b005960101e810007102d040c840009000079100c02c010001c85028903000702c041640c1202c140100380c4885083d01c2558995145420000d58403903125205000501644081c0402ca501c80d0080704e040e660001201858141c4a60044005000081c42942103028007244050b07190b0382c0740015030082071a48001e41d220854003031486800b410315480100007002544482032207840301c9081e1036414110803131502d49141940300050410030007481403203903640300149840c10150035074008104c421040c0c1e14444141d0301c8003010b0360f442d441038030450208407070b81e000248160300300c1d0015117520740b040c940071030340f16141c15500003a608280c00c1215400d80311007411940180d00946080e00e41e40601c014107c030f501d1600d41e1235840a400890714100104a98540107009040043c00044042d100c2c404c0ca = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 30339582 1250 30338332 30338339
    0x6090b070f080a0b01020a0f0503130b09010e010206040c15140a120b03060712180804030b0609100b04090209010c050d020d020c0409050c060714070303050405040b1002060714040f 79
    0x100076958030008040070410307410100c1d61040c610320505001e000c041c3c0041c03891040a4441241d202c071740c03035003c07102880704000424404075440341d0803009000c604c15503910344c25640c0014040001b00300049046500400c100b00c00724105880c40c9017119040340e0b03500314990070710204880d009041880348103a10000a8a0856180d03c00c058007001216540100f0a400700308041544624040c1c54000020780e050500b0520241c665100e03240100310444a8840c4e2641075982c1200c0c1c1c3c10562055417812000810041c0c5414664001b51b444443c3c40400a074082c1460a01c400d2801a401503640881d070100c0c2c1d00f13905900451403840c1c41a041411603c10740617440f0300942c1c4110280400005002d4103603030100d070741814012050001e41c06006015a07242007001d001e030f960080031050724010090346030440406010f007d540301031401380d5100e55403182408203010660720344a070030324002e42201040c001555800700701550010154682502e100001d000005641c1c01f076600111702141c9480c0001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 30340832 1250 30339582 30339587
    0xb090a230612010311120634090806060109030302120702030a02090c030402131509110909010e010801180804050904030c0203010203071101050c0403050a14160b0a030e06010b04090906090b07 84
    0x141224864201925402804000e210384d0080400704c549295008030045583c25800b403500707411561686140128844030030b000300c80501e202341001d5000c0351100005001c803850611000394401000e007403206066240d030b500203559202c5451110300c43c640116141007103580511081c003240da002400c1103034a081005105e40315605c19201240b003a603005503840c150000b03034000e0040c014840d80201c45024500b500f5140504001a52160b0b011000c200721070307060780c50a1100e4041d14044e4450015581844207850031202c1d0010504032030084501c11900050209045038152001079411110b00e13101e5107400c0d211101140c2c00298903500200c100b110a070361050804141d0180a030081c419522000c40c940814412030001602a4005925400108460307046450070b00315200111034460344206001001d02a003a00b0509040b00000340b1100c1c4541e25019448081218101400c00c6501d8280002c84d248214030070408039030703224070100707040c008154000d000403a00090b804140b8601035900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 30342082 1250 30340832 30340867
    0x90904060c11010c080a0e03070209070c02030f07050d12030213080607120e0303010b03060312030103110a09050f0a050621010501051203030405060402060d0603021215010b090a2306 80
    0x2801c00280109184422410140991610030030b0907210120251221a501300151418401c0130495200c104844001038403140d40291040d6050740d40c041003620b840c07040605241d401c010203d10f607481400c05115550380d103d00b0101c006e610100c01289800038420980c0079000d800b1030100c19207001400000e5010000c14181d1040714a503031400707410510741e00140c0c211f962409066130907900500c0180190700740740d0002d6800c05c5006003100e031001e00e912001030807940260001c441103030b4540d040c1e140038201020088003602204c04144044d107408610081020300040030700c4902a100d2011414a07165132105022145001110643c2e4140031501c050282c2001c1c0310b0300b405800e001c094103600c0348001c405e8030b002d00d900402a0280b80c999408001c402d8000c0746100c80b21960715040000160380c1c2889001541401c1009454941540d12201e544003c05a0000c0c3d034440c02007150080a40e214545070007941c4003004c62981401211060031401c00740c01d020a50041c000060307210340041c031b1421 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 30343332 1250 30342082 30342101
    0x1f170f010c02030408070b030a02270301060905060d2015040e010b040803040e1b03010311030606031b0607080d05010b030928030c020d0c18060801090f02010503070509090406 77
    0x203008a00e046601241d5a10030351044000c1030f004030400303018801c7c60038001d682000a009000d0b00306503065980e00c800d680740120000508546100c1c0d4001d5050a0003100d0082c040003c00708060710b40000425683d404000000b04024070100190070000072810701841c0798000603004440212212104088a50060044260740c6070004000a51751248808035016900c0070000385082030314000414103e040c0260610485644030f001c11301880d50398101941c001c5014081030450a801103042c141040009802d040c000c2c0c102c60070000030700c201b80b04248a83c2c2401c1d201255100b546082000c52801096000c41a950401000061034600200698040d060480560b00b100010240001c01c03108910340100b03001040069035400f003401800c8107180e44d8006468500707103402d1b950b030b00c0d84014916040006081c1001d001812607811a21441d406040c0d4007008010443c180e84400d0307404d0f03e9130380e0000e0401131f0000000b1f0750544a02c084c1d555450300a02039034003600341071910101411030340302c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 30344582 1250 30343332 30343363
    0x6020c010b030106170a080d060504020f210c04180b0904050706020607170a110913020a03060806040b0604020903070e07021c0219021207050319020f01171f17 70
    0x20003003400f117107a40e8940b10052031000200700e106020355450049400041030000031035034504001403251228002005200b0702c1181941c0e503a010100c450110325041c0752445405241c0b0001c10511580440840b41a11825110380c01250021902d2401425a080407070340c2081585c0c0600040010008121041d50703966000d89106507200c10048543c40381410411105096010100d040001154030450582541c025031a140c2100c00700850700611802e904004041d60000e070203041c040c0d1502c070715006081028054506401c003a00c40c91807610004c1c103800e00c81c903400103004a007035030108100001001340c4202d080462030a1000a0344a40d5800080e07103c9103c0e41510030b004034404290a4045442c1200c0c00742000940d40a002e10603107070080b2000755116403500840c90fa60200154140035074280c070045021001c134418405400400d080c00d030305001c0c0140210a211784102c40d00c0f64420104001403003240c1c0b1103009500080344650185030302180641442140440c040ba03000356800140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 30345832 1250 30344582 30344591
    0x3170a030c02030a0c020d020a090e0f1204030c0e0c13080d020d09050108070e010216230901050a17010b0913050c0109080c090a02090405010b040e0106030b01050313030c06020c010b0301 82
    0x200070ba840e4410300780030400182c4c05450600051a22008681c8401c1c0087d00340003942c0d4440125400300c0f00082850303600c691142c00c4108619108215800495078030760022030400749550354420500c0c0e0700340500c04a2411082c001000035107144d060310412001a0640c60700d070340d915044180c84103820001480140949400030040c940994045400c449060303540410541e07594800701c45a1410040b403d0441c01401420345e81c0304e9200d000c0c41c001c0c110700f40e030018502920301103121090003800421070190344800d004104540d1400054402c80d846070540c28070084141c24030b40c0c01002d40c0004c0700d900007180d00c18000700414000c0002d1400707208004a400c1034442c1c100560751000c0b20b118003880c9501281804038541440003440e50804480d400140c01d0030030250004080d918260041180f401000c9420030001000d551014014191814200f0900080c500000c100303100003030000101c44441c101d1901050320584040c8038031500001c0464480c60403446c0310b800303031084413a96442503082 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 30347082 1250 30345832 30345851
    0x402090d12020706030b0a05010e010c02062703010608031b070b0d0504020f040b030c0d020103060905010608090d031107080a050903010c0302130f080c011b05060f2202010e060d020403170a03 84
    0x80c80740c210345030001000d887d01103140000440304407501140141c1040364540c0320000588a4101030031541c000000c0c40e004800c8120300310300702d000300c42c18020b110340e05007a020040a0030102c1100c9110103a0300d59051203507840d1641c82d00d00f660b80d81c0154280c0e0000544103041e07551950015019520803121100603414060400c401e5403100200ba83c0d042e0403580d100015490041900600d0718410b060104010341d541c1030003422552700b41e00c803501050aa000300507040c101406000d880307501c1400c00b04040300d05088030740c0322405812401030260600141c00185680580709855058500400038040d02c4246a002000303900a00b0038040a180b03203540c003041c0210304901500685603680c00500104854000440305101171001031900d0358075104a0101242080c800b6a11407210701d4120300250902c03a00b048000310494a1814000c42e0007901240141e034010669000480120391031a00c42c04c0c40742d003200080c441c2e940001c14074505141104041002c11020f01460030750703030310708102c440795 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 30348332 1250 30347082 30347087
    0x5010911090109050f0d061e0b0303160f14010c0207030303060b040308220305030406081e06010507060c02010b0d05070905010e01030213090c09020c21090d0605060402090d12020706 80
    0x601e5003402d0116183c0300d000d0043e4142480c0040d42000000e0101088030145c2e110f00d011120703842004941c15004c02102c001d40c402c03a020703030b034000c1009070011440c11300c0402d4810520500420024034481ca501c0c04103080c01222400300c9609540c110003044000c550000c0a075480516200880c0400c1c1404000528420b0345429542220b4100d0075175032424285000110812240c40001c26407144001d0021000c04c004001400c0a081103031290f04c4613003030428203c0171524207c00f050040c14040c40800c00e045e41c0c80010340392456803007000483c1600d100d9406070701401c0c0100002e50440310b8180c00009000d4001a00340844544410802c001c0c0d88520a011400100740006034000b403083c1d101214044d103590003442054003840f000c0c0e01084d2201e000d0380613a40b0282240145600420401150f00b00d0740c1021940c0440101545180c0171101000c20003404002078049c00e030035991000100281c48603011101e844a0080c000c214003501c0380b81401d0310180b151a0000188140b5802141072130 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 30349582 1250 30348332 30348337
    0x5090a03080105100516020d05030c07030c0e070c0f021206090a060f020307020c0607060204030c0311040c020f060613060305070602030703090e13020f0d0b0406021908041112070e0a05010911 84
    0x905949a615160a2011401b100d103074840303080360041711200e44100491014000742c000c0000c1507002d0b10a070742c550308050740c4c1b6010036000100ca201402c000e21480c250484510441c0c998004002c3c41c1d0074085000042c07010840103116410f40c014401000310044000c80d01d400e800c0e100b060104038526001d01003008a0004444c0c940150f03011074498441850050003912030313148520340242c0342507180e94039140d60075016441100c000d00300040c03821183c60940104000b424040c402059614080d002c019680c0304094003860041c140301c18100c031a11519007000d006150403404681896aa98500035a2940001d400703400084001e0300102d000d2400036905070052851030660b00319214242c08001407814188462540b04550070603560006418a040520480c0207440068907605841d814214200c1d5040e890010844084104000a4040c50703011070781241c142c0c0c00c070130041290407905180c201240c0004000000301c004120b10207095400c128140e5207043c1d0180a02e48454800c0911070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 30350832 1250 30349582 30349609
    0x902040602150928080d020901110109020f011d0913030e01081603020a030b120a03080a020a12110f07151d150603010213140301050c090d0605060f0405090a03080105 73
    0x2078004103040040300c052040042e2404c0f90f084807086044800f507441c0000340c0e000c0542e5000e069000710f451962580c2144000701c00c078076600c00902c00c50b101580000e1122420812490600a0401c0b4000010a0281e8440c0d0b2811001d05000c3c124280442150010034030403070200c00049106210411035481002c25500800f4220a010454100844241d000e90001000c0c07800b011b540328185031050382d41b2540c0c4c82c00b140074000644a140e42e6424024883c0ca402868034220600401c5080c0049030320201e1010740d505224000070b4030400c2c501b2908440e04c01c4428000b040740c4041191018043c00410103042e003207d200c03041020042841c00500720b18101030342c4100310382142120b000c6424040070019070024005000510302000d11a64400c2010160400410341c4440d100001d154242441001c1c0c0002602d4031281c107110360305001810301c1000000c028100c94442c40460060707113030380304010440240103100784090b18004410a541e82d154010550001d14103800028250401555a5034032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 30352082 1250 30350832 30350851
    0x210a090f060504021f0503071404060c080c0f0109140f01050705090402031005030607030c120603051c0311030408070317072703021201050601110106080c010309060b0406090204060215 81
    0x180252070360002460000c1043c2e030410704100b2207820300c807441805001c9804031522150b03100d0402c20130050140d5440100c40e20191010001803021607044140a242264049513981d07554600c0c1c00301a00f880080240c08031250309014500c0108540407108003888003081c02200d07541281020554265241592410080303a801c200f000220300b02500111350001c01c03501e0034079a03103640301c01007890510110b4401c000a0b6036800701c0034216074044c1c1503139403450040d02c080c1300f01c604544405480b0003058035950811714118000810450103500221089080328922940701c1c0360600b04503c40e40e00c0040e04030000b4400b02e00c50002c0958040b6114020344803070795005035800300001e850018041000380325042d0740200c100000140d4564404420081c4000008600d81c1041800901202c2900d01141d01903410000f090104c0040004c0004440d8000d20303000c242a203090400d04010210141d50030780041c10f00c0004a8000407a800400894950340d0803100d06402c02a84130820404c01d070ba0f41b595 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 30353332 1250 30352082 30352103
    0x1020c0d05070b040209060303210712061406030702070f06090306050109051504020a09031506050103050601090305030703080c07060c020d09060507050303010b22090e06071e0809030906210a09 85
    0x15081c152400d5a0100b400346c1100d142c001c40040503640b000740d00450301d00301000ad00400010b10b030f00c10a00d601c0111742120600050b400e18035052407440034440d509019000101c0004c100034030812100c8000c0c804040349031040e548641c3d008001201900060746c0c12030401c400081c0400d13140c402e95200b06520051610351201d03040410010358002d0021070104100c1070400300210304203c011380003a101e07409000400f80d140000140503503100802180c14407a0800041001c240040120307002e082e407500e0886441e41e65000300e141280140769015149038a408071380d4112a80010704184512407540b030354109a59582e0040340c19218050000b00503820038001000309a0000c405800a425560461304010704942032840f081e8035154402000e4903224800309003109814010240c1050340d86c0360411064106041e620840302c00076400c2000c00071514001046000240f003561a540c030028105540c582c1003104d03a0842440c0507880300415080800030421407061417040800311a4004007051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 30354582 1250 30353332 30353341
    0xf06020c0d03020708150f01240305040f12030c02060c040803090103020f091f03050105010f0503010e27010b040501290706060b0708030f070206041e020301020f03070201020c0d05070b 81
    0x741d00885190450642c4945840441c60142c20704c0711a100c6061540700c80014901000ca41c132242d44180d0110700008030000c3e054013214040078070501c500040e410041800e0b152864034461100d01d145d005410249010000f013145503054001d13111110080c1e080741c200307840340c2d40100d0407840740b440781240a610030042c6540c154085d8019003c1c0c400244485030924825030042070480314011500c0655880d1400500c0780d068140c4070f014054002881d01c2d0422540c01074020f003d41c8010700840c0b544000480014040503d00c41c0040701030200d90710b8185003011118544c038060080445681c2c800c5013440008111940a6640b40109080401441400c900306c5055960749602055040d1a040d860784800314074540c0c00c0004080d003902c20020742e9580e14160b060508e5103275004c0c0c040e03030454000e04107100116200b0841e4100401444200c5001415a803000a00912030190313224282c150110800011507019409400c200d64034005036500301110a40440e101c0c07152410080c08801081c001c47d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 30355832 1250 30354582 30354589
    0x91b010e010c0312050406060f0b16020616051f0c0e030307030f1b03020a02011407020d0b0a0207050f060114090403080115030b04090b070908070605030a05060616050303040c0f06020c 81
    0x207181d66400307403d1021043e030000d444c840694404450540d4981e0f1110401c22540725030181d114011300c2c80108050030b0807e000803c0c800d81c46003007400303031160780c0c045041d007082c050301a00c4c1c0d035000e54030004445081c4c000c01128205071004541000307102c1c1c50140768041150240300e203050382440040c0a5031401d071083c0d60964070384219104080c204649000c0b01c0b10361520046c1043c0200c0d000750020320b039080703075440010f250010020b031a0a680c00144030344001030f25145103030654154825006d00c00d9079200c1158034024024940003070040d00c215440d0619205001c207405069464a1384501f05d01000e0750140280f2000c20740b0010002098140100518a5a91030703903030300c82060b0b1074049001050f190004007519100300c4c041e503044d045042400211500300c01040000c1040e403024106441c642140501a40002415103070142d44070750015210766503110444039540059102c81000034043e0a120780e40303400c1104e084130b542d410384a0100d80760b070700100070004403640c81d03004158550129091 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 30357082 1250 30355832 30355847
    0x903120e07080f0304090b0609030d030902010315090203091005071b050304050d1101020601060306060509010c020609031905010b010801050a03020f04090c060f02010f090201050702060f04080a03030203091b010e01 94
    0x1030380400d009020000c14070302c10921001d8104003040b001542c030780e42081001c8080b142800c05807171003076070100b0000200e518049480800c4030300ea0f040c0081d10030240c0c00143c001d400010a40091070700c24000c045191030b804da02071400b4400d454115002e01070b01a0100003160410390b4000c01141003000465840100c8200c0f0080c004d00c00d0041e04c0c01c080c4c2d44c002040e0100f1010728111084942c2914844555030b04000d0180101854030341400b03200d14040b40604288160300c41c95041141c002e03882c02c155110303042100c00d00c0c0c80250458007140d903c0800100c40c1069003404a4940d4240180e04a00d988944481410f0320001072a1b0100c06203035034200420000101960742d009a01d0b4420340000c520400003070b0001b40201e1b02d031450070b009004c2d0000c0c2124001c50403007501a240a11800c05030364082d0554403801e90540d09659500ca030311902003039501490788a0500d900c50540e065040540c5074014600407070400044411031420300c811004604410040c2a00003690038034070680e5907104028 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 30358332 1250 30357082 30357101
    0x50a0203130b10121101080f0c19020a080409020301080d110607030e0a1505091011040b0304170d0207150509120f04030b160906050313021e060304060618090312 71
    0x24618903695094182150090f019040e01c0d030782101019410170f960001151076006418203040c20040c6407142c0405003902450807621040518000601e050382c0c020080682c0f00c41d00015401d031100c0e52122124040c1d44240104917042c010300e544203082901800251802190000280c001c503980d9200880043c203002480c0d400078400e9403030703540101c1c2041c081040720544a09021820f8038247d07194618214a0b100d0420700d052503c6461500c4030300920540e42600d809420303d42d501d803658184182c40b50300603043c051409000107951200c9440543c02425002d2140c0e00d0503000c1c41032012042c044820444402c0c1140c1c200c0e0109020720b02d02400100f4459041c841030030305103038480d140c2c240380110480e2541520120340c01c0c0c0c0c400e203030f400502d540c00514052620b03900c1d510b0a42c40b503070011100034100034000e44a08500e8100e070b101d952800e00c0381d4100500483d444e0300d050b0400c1009050300b4132901c281d250a9020340c106000c841d005075540c094150300d5110b0701c20148a07422004001e60003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 30359582 1250 30358332 30358351
    0x2010c2c0a0e09010e250905060d0804060e040501050109030f0f0201031e0509010f0504050727050c0d0c0311040b1303060606051b01090b010b0703020c030105010602030a03050a0203130b 82
    0x6008608015801803083c043da034020700010b064004815401d142c82d201c0c14443c28102c107003040f40007000205104030300a41d800b9240c00301e8162101070114207a500b1024004110440108010910650203040483e06150444007032240d642e954005541500d4980000b91081c001c4201c100040b40d43d1250071000c0a2040c9000500810903844881c19104916040441d054136113062049000c42400307441018134030070804220600305541c0f20ba907544d03a188601d403410ad5a0b2403111002d50454160043c2041301241c2c24416490040d001c004245c0c012010101003e01c0e01c04240b078914800d229081e0110a50003619140500340303142640702d0b411148441015280396071002c80060000d001d2000140300320b440382901e030038415070401602401071303a00f0306642c3e1403c0380c900040b80207a1034180c1140c00240110381e4aa0341401c040781803a1744101425015030800c00001491381c0d000004019480300717a5020072040d00d50610328026031000747c030718034600d200c52182c1101044240c1c0e1103030340040c2c200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 30360832 1250 30359582 30359599
    0x507081902100f0e010b09091c021002030708061801061b06270c09020304080403020f030a020d050c120115030318090f050a110c0604030e0a0308070501060602010c2c 73
    0x42c046203081e24045882102c283e52600d0081804da1000d0094040341d11007100c074150203140c041402e5541d940902c100703000d0320368640c286000080c000e1219130714a0071204815540e03407901c0d66015150000681c0c1a9005100b448010400b8485a00016040c0e50f059074a503082d050103078299021944034000103a420b01c1c0d948642c0c8084078003104504a24020410201d140500a0308040c1601015680b2140d4013034010000c1100081181c0125001e07203a040312890565441000441e240c1701c4d000b90029041030200c05100148840001e414449800440344003001590000d452800d075284484405d180c03201515081c4000390090541c806d01c401d16a20a104141c1e4403140f45013954240041c10114540d640e00340b259041880c0110542c0c003070342807101860305041c2c040465491b940244041c040000300840c40502d951032000d45401541c101c402140c40300018104203000f8806c3d84074960140d0303e482551642180038032201e8807100000102c56118204c2004490403113580c0404659010302c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 30362082 1250 30360832 30360853
    0x40b0f1905040506010905010f03120f090918170a0c02060706020c0312090712080706050a0e010903050c060702060405060a1a0406060e040c020303060a0b0729070207060507081902 79
    0x2600c034151242d0f0007040101042d514201e8500c007204d00c10f8000796002c505403a001e101203428000c0851203caa5413400030f410780c01d120011103d480c0340c0d4100b42c1c04141400b0040031400642c4901c0c940c828040c454002249080b45000202c521512015402280c5150a00c00c007500d06035010300480d5001d000007618181503070460310b05507402484250301c05201e200070b000e0303d200204501e00c05000e0324507803c60380780e46545499290703008000300103011503200d0f40050001a43c540205040895020091100c0e920900c1e003d07200d5007001c1c2c0c40d02e1171403013100005081c5070300c0050f041c1e001c2c94103c8040c00494544000280c05004040001c10302c1009407a02a00291590307c174240061030700c0d82c6c80c0d1020006200801090700c030704620100440d4410306c1401441c0e0f0b02e400c20842114a000000c40e6241d0f03652900b4100804a56070982e00071103400b0400d082c0392030102056114102c1507090b500115211507080c2e43c0784c016100c010f0046802881040004c1e08400f4002c03210444600468410511 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 30363332 1250 30362082 30362131
    0x304050118030206160201060605040e06030f010606031e0c091a130b0403020301050f010806010b070c030c0b0405130e061603140103050102180105090303070803070c1b03020a0806040b0f 82
    0x18078034102c1c0161300013410440382c0760341c80e8103008810352244001c3c00304610700310b40246903000342d01807080580c48800c082102ca5600300301210040e01c845000b40030341542ca8202070014203003604c8084080000001d10b8607100424032682166101580300d04c0007107810006007100b040f241400340c01d82e007075041111854100984014000803c000c0e08040e99031800d52042c1425620050900311100c0350b080c005000740c00000c2030081c1502e400c800f80b039850300c015041c034109804040c0c0c0b0291900ea1990030100340755207990020420b81d10300f600d1484000410901d00c4044610421255249070403400204607000920482c0c8000c0400a140103d243c3e2244036201c40841c000780c4c02100e050f0350002d66641d2000c03401042c04a020030900b0308a00f001644000310740c030b070702c03840308000c140f56000800185160f005110641056400030030480300c00d00d0241c007505c01d018607400f043c2c0c41b0b41540c0f40006040380340010700074810b0740e020070f551405845942c21901e61000c094a4281200d8003031420f6054500f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 30364582 1250 30363332 30363371
    0x11707050f0f07060c1103031b0a050706021c0617030403080f120a0e0c030705240f0403030c030e06180f0f06070503090a0614030106050a0c021003020702090601110705010503040501 80
    0x6000f400c000604401c20704000c1c240b0000d8008051013a0801d1041060401d50821807205149c2403605507640c9000b8050215454031903054003c261610210751429003d403030609031000503400c1c6604001c42916140300300d1841f507801e62103102c190320400062002480702d50141444030117042d926410300c401e0150821998000b16001250f9503500e0f171045c1d400150402503014119000c1d0007800c4000e0a14010403c0c82104100301c0e002c490240b04200043c0c0300c0881120080c0342d0769144181c0b03c6444c0d01d0000e0810100a03c1030300000c0c5290711a0505180030411104031940380020316400c00001e00500030b4820740c400d00075a01c05100340411070151150401131424521800c0610ba85284500400c554107040e500148204040311001003415070201c012641542c1d40741c241a03071107241c41c65040750311440e00c0c20002d40103001c000b11243d410750160044c04200d4401c5500a40070341d9404011201c41990540ca4521640009000c010740d5001d00c0045400a01941c00400d0380180c00c0d04034068138 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 30365832 1250 30364582 30364597
    0x20a03060f0603380904050a050d0f021513020103090c0b0d090c0e04050303040f060b0a061e020c0a090c0207031a0108070803030c03010501030c0e09160e011707050f0f 74
    0x780c5a44e4542003c04920301050714a021a0015106400e10807503d500c15001c92100c0344c0c002c00044000c602401030410040d01c0710ba50100448100351142540244116000618180540b02c2c02d0207000a5611024080b403090300002003d5040481c1c940044001d0031202a041d80d03090002e08010480c1b484180091021040d008404034108049181095140702c0380d9100b40114200c1c03005001c0001c50203c11a40c02c2900142c4402c040c02c1c050030154010700c0b031640c80540c8281c02d0000010701f00d4000c01084e254410b022040d4100000740c4109030f031145458081d255000306d4000040c41b1380100d0758403040460000e44112148180c50707949001d22151a0402c03114914500c0740108070303082082041c1c2024101c980c011f1800c509045241c5010f9000c1806414103154031122a080030511481d0300c600a0207005054040383d00b007134440b4030822840b039020600002e1340b60680b5115540103d103842000b54807403c040b060b61381d0780c010032031700c0c0c0e04101c00120701d202c000c00403100b0f08410b03034001d481da2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 30367082 1250 30365832 30365837
    0x10317160c0902040510020312010303030e07090218040e010c0212130b0c0106050916080c0d0b0904110906010507050601030602030a09020a030c0509070c02030309090a0e0312040510021309020a03060f06 89
    0x513142480208800da10024032540300b1544208089200c089200589904580d49800c010440d0701040c418107080c032071650041c150461001c02e24240100003180300c0a400181628200150301c81500d00030700ba1200d003001c00d400b40e4004c05011a5081c401c03002410520323100c94442c00e02d02d0311401c88a20650002a0200b10303691511000e0056141c0320420b144c1000044464450358281008040c20014004003000004100800d2501901405030040d84c00d1a1000700399a42a12301071821070018821007103000d01a4000d100043c0d034950096088842c460341190081c0701980c6155140d60103580024512468151140c0c1d00c40010388030225400042c40c07080c00504801070901041c849015001031402c0e08100c0e643d080346025032404000c0f1034607088250b602d50650f0b13490f8a1300d040500f503219101070481c4000942c01c10300075900017450b401644940203440304400840d03501c105038001d110030100c208401240400a04d1911b900410b01a0a42d040100b0304607980d0098246012495002001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 30368332 1250 30367082 30367087
    0x60f0c09030714040608010501051f0c0b24060306030309093105190f0602090a0509090304030201170906161b2a0609060c1b030302070503060708010317160c0902 71
    0x1104d113000d01624001d0300201000701308561601d00040d2100e5000410320140214010301d403441d8910442841180f40e17080858101103040800340300194038004201c0c0c00070b03400e00e412003c060386031460031a030191500030002d50501e03003520100080b1410142c5840c1e83c0001c0030f400000da96086070448078884000000c40c0c244010941841d07404c0002020240000107400c00d80100018941e00f200514107030000340041e100e25110000c6060910301d07030002580014210100904108008028801e40c1e10031390703c0000180454503040441c450a403103c603215001030f00016840c1c0d03000312030401034250920340300481124490459240d4140300c0c0d000c0d0764820a510024a005034407084140f070700c150401c00000d2062504d40002c0180e02940910b03020003611900c9030f020b108580c0c460072006010440e0103180f2960300e1801035541e1a45100c6c2a0107409118005070000b402940d089040b02d80118220310b481580803001d181d0b40c2d115034824001440318040280105414401d00c5000c0d02103a140141d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 30369582 1250 30368332 30368369
    0xc1603050307120e0904080f0d0e010606020c01080c03010909170307050405040605060306030604030f051e0702011b11040906020d0203070206040b0109060803220b0703050406090506040305060f0c090307 89
    0x5040d05011030405043c09012128100344c1d03100c14243c141e000e6000200b191701c8205095100032140701c4d240106c0300040c01c118200188d001c040d84020300f00c445680882e00c440b100c070700040d80c40e041b003100c0c040403906041c4010003100a07203400410000b031080260f003031310125186810255070803d580700740005a022400744030700d0070148540d4010340030840d209401e501c1c0041c0000d917640d400500c01000c201000b00820030150086040d1a20310400300040340c00c08213041c0749114180c100440503800201140c8007007007a2449080c52081c1079410110311445490264140005001048000c071601942009010100b01d841d20140d805028640d018050904160404144000e410b81040419925042040101540000c01c88070704102040d049150740c44e0030301d10281e8121455120410018000554400309035021005000380c41194640140303094851041c000940900e0000038042d03800100860035000784c1101303440e404800561054588070400300800c0c20075107254800100c000d43c503895103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 30370832 1250 30369582 30369593
    0xd0305040b0106030612030c0203160b031506070302030703180f0e04020310020a0905041503050303010e09100b0d03030b040b03010213030b060d0c170304080111030601110111030601050c1603050307 87
    0x214010500d504e010b02c809400d0031000030102c3d610040090911414000c1082103480c14844000c0078200605400c0f640350b079411030780080768030031200c990718241510175614003483d020b804e494150b901030f0700444c00c0c1700386aa82620600c211401d0310715103030002100056082c1d020310108001c1c121410b6084080c0c00d00c0d1042c913240440400d003000c1210b0051112036122688011031100721403003203d001c20680a42c0e1035044400040c0d800c090818000000081046810311000c1402062620221094084452440310032180400c41841e80b00b8503040c41c8a0201e0702c02c0e0417148803a00014400205104c43c0c1e40000d003241e001c203202c90380050b00200104144107803142e001342e00400c180d0309114000034070394400b5108102801602602c2590051461401c0b4081064030b002c0c3c41194020010340c00c04110380e00300c5400c00c0340c7d901e000070f0b401c1414145880c01070084040740403074905900e003551150b0f00196015003220f401c00c41c643c407441d280ca860442030458004015400b031006107540b0001c9040c0b0703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 30372082 1250 30370832 30370853
    0x3060302090a20070309030204020a030e0f060903070b0603010e1005060f0105030903070803091002180906040903090b2101030b04020a0f0f031205160309090e2a010201020c0d030504 80
    0x190009140c0303d40003070001c8110030034121065403600e00c04d075950040d1a0a1350b2120042d00042d410034808940c0103003054241c1e1103680d4080c41e450031034044440c21035a0540d00d4038102c3d0329100c9500148442e000141c0360007601e0fa006440100086000c455407492940703804510400c28500b01d448105200041c00c0448210078080400e280082c80c40c036200c80034623900e20030020010f156400000024078110402e0000600610304c0c42025540d41490481200c007136070f404000b092051440c1d00c04501d0600c0c20b8031810307000342d0389915400c400e00e14150000c8001e4000b080b28089000d03a0511500f004034070301a0040c060340c8982c1c2d1b0281d003400d042c01401500803960b0040c400600f0791550512104220890034000c40786d000d2641c007034040c5160011901130044001c070000c803c10410844042680003a41803042d280c412404000302c00c0c40302c007941c3e9210001d0301d540510101402e20710014901070f5040b00b4103000706000144c03030b2001d08000f041c40e00364503072500e000003a501d005000400904091 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 30373332 1250 30372082 30372091
    0x7050d02070609050a0c0f0909020a030f02030c22111804110f0703031a01051e070c030b18160515033d080319050c010603150905070f0303170a020c06070306030209 72
    0x10800c89c0842c0740e4040381c0e8000301e600020780300c03c048800610466804110240b0032140260040840b095590341d403105440c1d81020070101b45013000d0703a8000e40074a030300c20703141d40e00c21a4644800110800c000d0100800000c014060501000c03c00b143c0094007000081200a00c01d0b500003442c90204000042c400556100d035a040003820041c000105041503002940300c500c00c01a01e5a030039440c90105601200e40e40001c001007000c100b0451054281c0803029404581d01003a110241102200c0c2070000900d1b0050aa000b03605c1c4008507182c46600c0702550340480b0340e94511400e0b4540070010449015a2900881e00c0368481c821070540450801c204c1c0000c24100d801542415100040c3c07041e002001c5480320204100411080b1400800b50485001580c00003111340070518224440d81c003038036410b60266840e104000c00052103c000c0d10001c812203406980391000b010305241c0c0341002d8180542130310140c640a202a407030081090100c2070180d40c07507840c006541451441403001c4004002c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 30374582 1250 30373332 30373349
    0x6050303120c0a0201060504150315410f0103030f0302180108131406180312010b09010c05120a080f07090501050a02070b040f08060f07050d02070609050a0c0f 70
    0x40408070414100011907088501044920b03280c40c12100d00301d0041503c5d42c4110f9005080c0a00b00d54507010300a241c02c26a4002c6252801b03119019801000f56040755103c4041c3d544800c011018100e001c003502d03540284403820b6001800da00240c48064040262440320342800010010010150440081c4034034007420b041c10750a003591321401a240f032600d110300e24180418540008c80d1312000360300011080e0f6110309030810181440e4003da40d5607104030b40700e025000d0030124a40500d0000015140c11140fa440407803410780c20701003c00c100b0f8000b4042c3d02d0500001d04908400a10240200c04000d0560028552107011480005080e860042e100c09080541c82041c441602d60101d510001d5030404e08201e03640300c110301d400702d140c0703c031075030014403a04c0022601090600403543e8180446050800f04c41d0301da1504c0350107104401095903c0300205030100441481c038009900a450100d003d08000100640075440c0c5a003020344191003154045e1032804103005110083d00748201402c030b403c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 30375832 1250 30374582 30374587
    0x80616020a02040507050909090106050a091e3801030b1002060f04081b0619020c0a0f060b0d0b06040e06070c031107080a0819050304020d060b030f0d02030a0306050303 74
    0x680000e9214500340d000a8000e80d00d4000060b1001d001e0011660314070405406036245280c8030744982e0092010b030142c03c0c4507071080030b800a0f0480c0b0303038050035910000100c0c4800c00000701050800003010b01c40c894040301c00000300c0c01030004c86989040740071115001308103039001c03265400040840c1c003021416481039400b40540d00c4030950000e142503004107154540107841d111414005190f01484400e040c2646401402030844100030941e1401a80220142d0310003240c10041c120690040b86004501544001440804030348484c9003500028000c00d40003c06840301800305800030030b42c2400390b550ac940901071210030b05081c450b120a03060514098072480c1040000142055003800000d001c000014003039644051b420301c078940091000004a5504508615200742190000c0b16008080098200c0241141e4003072011207210710b03801011201105580e079a10350051212441494151041000105901c2c000b0040500c0e910905e800441d01c07050500b000074261000c41d04400e0007600300713 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 30377082 1250 30375832 30375871
    0x50604030b06010c06140a0b030f01110a0c1103060109092f101b0c1703040806011208121005040b01020318061b060426070309030201050904090206040905010806 71
    0x3114203070b000302c42442c0078030a030255420000050486010040d07006200e40080c00f007012400d131300680740c941c000d070240d800000b15a9541407c8135280315808272124001c103e1004c0403417161001ca10010b106200c00c8041201c1000800d2400d00d00340c200030103680d594941c56040c42400700702408406000f0b00005c00100601c0103284010b00440c1c0494003036510f4441141895014200105080045000c0300c8001a028100303150034a0403032292803401e11051040c4c840c2e55601000f10740a840550b00140307410f0f46450801c0c0c3c2224a40383c3c0c160b4003013005110283e402040c5038007041c001c000c000c51030301e00e85007054100000c44d9200c68180381594800c01020340741000c001c003914130840003180c41c2511043d0040303008945000701c2d02202a103000b008100700400200c90720101102400100d00c800014143d14190b88500c20b440f8040d000c2000c500c41080150720480042c148e1034405400411145110340c0800d007203411541100a58540303030001484070020800c21107074821103041500307980c044c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 30378332 1250 30377082 30377093
    0x70201090302010806060d02120103020108090304030c0312090314011a03010c0e04020702120f03071a0c070605040822140402040302061803010204030b0a020a0206090c060a11010b0a030b0f0105060403 88
    0x5407000070306002461000420654442065404980526006550b1540740000c00d240d854002d000407800300f05050301080382d00744008140e82c00c3c1c0340c0c0401406019404c1d070300c81c80e000001c071403c0b0408101d02e004000c0006020704110461f03181c520030010940c1c8144819400b10307607681d80c045c0350090b0715051705070b03030b0865101e800e6251600090320010703076030107660010a100541c441c1c1400c488c1e10519002d4401904000000d02402c0e006962024070b50001013100c2c090f1010584110012000034401e58001c00c115510603a0010300c10266140307025100d10100c0d134144081c40100003420280780701000101c3c0a10300340012804100d07800c5242c40c0c1194002049400b0740c0240d680e10621b070813640ba003140c0742513040320080c58200182c520646461243e480184d440b20002d140140a0400803a80880000403d1517492200900300d900f03040100c82c089502c0c5140d8140744034250748034071401003d030300c40b4200da6020318000c40011401d8030b030806005512040692219002e500e040000b080800c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 30379582 1250 30378332 30378347
    0x30b060a1e05040b15131a0a09060318050105161d1c060b0301020f1902011b05090f0901090608060c0c07060503040302031c0b0301060b07020a1707090c03050708060303070201 77
    0x2c01c100c800240342e150075000701c0c00160800c410090101000144141a44a852021022130b0080b420300104010078591000f031b54051489030202061040e04c0502401d030098000c400c4400f854a0300c2c1d06800705c80e07202c0500f581e07000d071020340040341441418040558800701410743c2180155503d50959905070116031141c5c4108441d10100380800c820004015007030704001100d1100030001d549030b42404071500d00c558003078070f110074016800007014001d02c1c0c0180200001c0410940d80e10704003001490301507c181e400080c0390781e8010407101000c003440d0f940c203014502900b42003500003041c6041410040c80d0041c058501b90a102050042142c040d0001034060159039403440e0850300c9868624050340356029840d4441c11009040c10400091149035004002e0300030203c000744942580c50400e03000b5882500e101940044001d0000c0c000319079802c2010b50810b40b0842226210b40c0d480042c1011100660039000019845500b40004070780e0003007030140c100f40c00714043e52a10724a40d00117007070340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 30380832 1250 30379582 30379589
    0x3070b0903030708030f01090b1804140309060309010b0315040b1303030605060d0b091003030e040b0609060705070812030105010519020c0301020c0708010c080103080a08041b030b060a1e 82
    0x5580004166440c1e89081c41581c1107194000d000a889060501b2000d40c108024091740c103016262401c2c0c1e104d10300e0b0090ba40d0800c2081103000c103e09407520303110110181a2070320b0000041c070040000100710703264070b401140714181070000000d80a90314820141819041042002207200c0315080c84041024941000d41100241c80c001c94001042d00e0103074050a440c0e4001c2c0d500020105541305007201540000866007030448664106a03903101416218803501d0001500150055501207090b0a00e5403021000c108002c0c4000d00b8420720000152071544000402c5800d600842020000e150040145541019250924601703540c14440001c1c540e02586113903004203186c5000d24507015009104116000c54003800035540e0b030f40c1c50111159100311910614002e5840d2100203c0c465108042c901d05072a4044649481c2000c142012112150301400035103400710404400d010345049042100002d511038404041d0600e025420850420324951186949424191440100d40e5814a43e403066 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 30382082 1250 30380832 30380849
    0x31401050402010f0c060b120a020108010609061b020301090f1a0105060403031d0a0305120a020f0307050304050d0804180905010506031204091a040207030203040e010902040e04080a05070c0b0c1603020307 90
    0x1207101904141e0301806288400e1604100840382c8c0020340340700419195041e90003a2074101e4541d996007801c8403402c2d10b074800e800010b04424444c0160382d0405002440c594001000805d4500c007507115034000c40c800040032110054803d110100030798039515420700400c0200d8a03e41030600d1918041d01b015101489940040e29a0380a0b0a141e91042410000b440d0008201d8019207002d190b0040d450340a0001100988148011000841c00000468001c80e41c014045c42c2002d140c50184942d034170260204540701074060001094001060a9500c410f004002001c10b00481c541003060071207501a11250180d0131503200c07400403841403c00c4400b147c402c041d000400704610742400c4003141c01c032207400d60701500018002090650000242064410300910111281d07650150340e000c900c554410b00207480d1030a40080c000c180c08030060200e40183d81040780c0380440b80d5031a4049098203800c01541d0000100e41c0c082400800c0100403500354050307144211031411900080d80d10700091068405 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 30383332 1250 30382082 30382097
    0x60307050304050a0c080606010e04060b040b280f030c02010b0901150207050402070b09070501110a06110903030a0906021011191e1d01170604150b04030606031401050402010f 77
    0x100f1104101161005800c10240c14085480b07400345515100706452241c00200240310a601d6441c081c03250b58102d40e0301a102c0d038903140c644680500705030040a03590281c2d203024044603003c0d5074410740250b0002030f90b0b912813071605101d21001e412141e2804841045a141504c6100642c9405809a0541d08032541207296119503042c02c178940403c43d00001c1d00680040f603a00100035138500094003c4401d1000c2d1030949885500440c1c501e0b0100c080b01000d0f500c0400d03034001184c2c081d4040301c924201c09a08501d0541e900012030318561114029400060300d00030100011a07060081d04003c03803896406000000e440441c0c86458003c26100c5070751000090b41d4010058010341002c0401c80041d0581920a900300318041d201c1e58241d202c540c00c0c2903002011142c2588100006549c802e000c0c0720410690301d8032400d1200800883c103c103400b55001c00c01c00b08140144e903001c1e2004501c10203000c1801c1d801c61a20524001580c0012803c0341e040609003c0180c1c0c00c01182140e003e03481c681082d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 30384582 1250 30383332 30383341
    0xf02030d0b040225050706020105040f08070f0b0103050604060b09070203070308130209040b0a0c0507021804030c05120c0f0c030613060b040501120203011a01080105010507030201110c0304031e020603070503 91
    0x80c000e00c034250511340011901c929402050041409100015000b1000e81d4907080d5030b180241d0a0762001c42d8001c3c40440d0103601350000408100c040d0a10501030141224011100d56850040e4003080c0c106403031951020f000c100400015002e0442910400ea40d090f40500f81404081e59078080c0c0c480c01024820100002190103844101540401da002003102101e4101420f01a5a038802542d982200c5405c0c244012091130042c0211603519a01404601c0300914061480d0b04400e0060b0007107080001c0044c41c6404504200240c1541c3e0007000300d09a9100d80031480c151034804030010039080ba0b0001004902c06075004144264001100360303045038000407615150700106510041c90750b00a14040012400a0a5285242c01c0e03d1095008010002c104c210320300600150040c8180040d002500510143d4492409801080c2c824000421030000542c0c00e42d19079003020040c90074561010078100207101c0c4298040b22a010903050030749140405401080032403200816510a00c031000001c075 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 30385832 1250 30384582 30384589
    0x30106050703030b040911090c030103080909070302090409030207080c010903020907030e0a05120405041406101101020c0a060b0a050105040303020d05030709170c011107050906040b03150709060f0f02030d0b 91
    0xb55080c2c031300204100b0052682d8a8454500c803450800c0740d008210300400150010404800c407416a0b401004103402c0c000310104220310107030000e0411003019024044403d50f0784841c0260304000703200c0d4014052090a0240d69440c08000c00005410001816000c2002d0b8035200000d54000007640b4021410822240c0c06070320300151044020410310901c440c0d01d140c0440900580107031142181e083c00784203c59100c03440e05003000e483c0142c2c00000001842c40aa00440b032150440641030b00141c1084086401981400d1100300182c440c0d41d11072940714110f1034541d814101034102403d095090a041d602d000750f0320b0021419490030300c0340c000b011a81490091808200901c800f401c59800360b0300300790381e5503241c00701052181e001c2506800c005020f1303c4017192060640e400980010b015035a00340400026242c1146003580501401440c11072141c05118002e11482442e155407100c10f1410500504480c4807085030010421035a4007502c00316404400c03260078010400c1e0200302d041450000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 30387082 1250 30385832 30385841
    0x405090c1f090501030501150f020c150315040c1d0102031c0c03060503010b010203070f08040504050903180904020d0b061207090b130204060c03050c03070b01170f0c030303010605070303 82
    0x369544801150180160003031070005070000103140b0303956a645259603d0055080d14028000c3d00340340e0100048042c0410f1296640040e85000ca06c101c548480021001c629801d6051028614403080001044000700c844034181c0c1c012001620104248054900010011002d48140c0c100f080c0134600c070004207030300c200700b6601e181c10488a01d040c01982d001c110b400070b2800c1d40d00200441c1c24040006840c0c5418841d07118561010b8024620b441c0c625030700c2040c2244001e40803034030381c1c03010701010805484600ca0a4807441111004540d903281c1d5105445800341466076607441490140c007008010f0322004000e00c0700e19401070f21402c41da240e44e0f001074182104940c205d1114071440b000000d01406540090f40c0510090710070300d080541d0320802d1400e0f84600c4c0103210124250303024110000b44a10000c140030841401941d041581943e2010710107442a8407092115103000103051000d0320602841c1d44c90301d955402000d003051580c000c641c076808144241005d00c8008500c200c18540241c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 30388332 1250 30387082 30387103
    0xe01180f020a09050907020a0305040b09040615080618040f0209070309020306091c080912030c0c01060e07030f02090307060e0307170a050105070f020c040209010309351206040509 79
    0x80d5101e040b055001400d9042c40d00c03829114146000106030b056001181000b0001d40607500c02e807910703041c11910b64165020503d81a00107a42d000001005104a90910344030b40090b6140200c41c20401c00b040544005c026072680082445024040060b806d06808000d056054500c0b1030302e42d503422000e0300241381200000e074060148004004411134081a0060300c507103600750300c05441c1215101101c6102049401d2400ca07400352002042c015030f00005941e2085d2020b42403458030301c2041007242580c81c5540f00900078540071040c00030007034041c0100d62a42d09012411400c00301140f0000303960b841c1e94841e542c00d01c12903104c00513540d2400c0c0030300c002074429680c0c041c55460340259450396070050713034005817015441c040204d1850351103910740030b5000d900c0d0350062100541080410000f940011840c0381450b9031180e4060005081c5401c1003504801e0500c02c0c0d4070784061070a4244003007040328540104240401c0304200c80c14600404a4001c00241c900240c1c65903010401841d24024a1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 30389582 1250 30388332 30388361
    0x30e0a12050105010503060a020c07030f0c0f09060509070c03020d08060f1002030d18020315090a12020c011215060c0206090604150e0d0305070b1e13110a0e0118 71
    0x302514188001500258104c1da8140c0c111011507440c1d02e42c0e01c0890007406c01e404090742000034100b002c60510a8001000ca0184404100240d602c2401d00c039080b00d603038081a002525000d0400c21850f0050700d20b4ad00c03a0075818855a03052003554001c1d203808003941c0c074600303001c2084081b583c5d584400b202680c05050190a140448070700842c00f035a20742200414007201c40c00c1125490800d9a10007404600d594043d00800301090020050a41024005e1501d01070303101d800c103c4800301d124400701101d09221600540780303642e01840014210070109003620400ca00301990b612102404000703503030440d146440e001548048a1000900b02e00c00e80f21641e07801400410045170452840c0309900c1e0020041d21005e51b00c1c00007000b806507642d403006000e404a002801002c020400f0340b00515400698010100c202d040f0450010b480c42c5003e9a0083d6400c0c00040401c08210f0380650000710b925040300d9140569291103112080c0701c005008448003440540012071961050303070000f0382d070041e031103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 30390832 1250 30389582 30389609
    0x80307230705011a100815030105012d0605030601030c051303050123070f030b0d0215040602010f020f0328050a05060a05040b0310020a020f0604120305010806070507030e0a 76
    0x210380c46440e4000307030402e0b03889500e400500203800e180391040d00b031500800f900b480005004004155205c0d00010310440c01040d045000b921260340c2849224007805600540708020018026041d072440c0041901485200340c08009014090f0407a00781d903448102442c0c041900940d1580488060092a400542015111401108114064120715048503901040904803c11880d601c0c1116000382d826102146504180c2d0920601c240c00024010401500f49580b048007980484c52b0000b0b0480005c1c2105030203e0240041070f070a0003071850440d00030900350b00f0904910940140c500c00504400100101d0700003980700041c3d1020948480c0c0141c150400c481e19100c031940e4042d100840c1c081e40311316900d00d00800c4901d0300d841281c9c0b500320068018075202007001c030b0704002540303c91410b106502c62000e403088090020486288518464034041400c100e045101405460040c1c001c081d00c1d070071000420414991040035514030540602c0c0600203500c1040100d24907a01c550007079040003c0d030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 30392082 1250 30390832 30390887
    0x10518040b18040606090e240a1127010207030b06060c0106080f010504051c050304030c0606080d051305010e06070b0705040e07020c09090102041a030a0b04020c0f060105010507030804080307 84
    0x3030794008001c840710228240600c00c0b4161f2216110100c00c040042180919010b1004586210850302d9005292200000b0300030b5101c0c2404c0c0e01c94024100c02c00301515160480b80700220f04205481414030280002d050103403d60b911000c005400420703040c010344000c030b80740f05e00041c02d41240000f0318852045ea074000b10400b542c0c5000e84001c84041d9064401d09010710f090743e40d83e1255076020b0915945245c1591501e590440f0118042c03942a5240b81c1c0f14070005ca00404184191902d10186440d0b0a03545d205241032011503046650110b810301c0f103007038420001901c0300c4007180c40711a0b104003054800d5481800c192298022500480310034a912420000d2a580009011200940864614140d136440d03a09081c20b07885540100c1021020742c40640040c52440d80c042d542100820001203680351118011900300d801c4449409002d502c02c0340400700501007480650302420342803070f01c00d00e012416100070b09178100160004000c0d140000014500d144520f81c400d0301e061410071041c010a03503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 30393332 1250 30392082 30392093
    0xb090303090415141f0807020a05030301180501050f01020607050c07080601030b0106080906090d0f0306050303030a021b07030314180d060c09050402070c12050a0f05011406010518040b1804 83
    0x201400340c10a00b800c1445513054920300210240b4009100420311000022031030021507550350081c02e048254858186070400081087c0043c0d8041d06103c2104820030801401800c2986c00692203180610f021185018607030341e010a2041e4040e00608180d0381d00c0780030f80d90951404180c1d900c0007540c0c0c0120000402009813540080341240c61540e10030303515072170301040f850325038800f81c590303c0c115444840c203483c1141c0103501c5000c110226080c0055166590700100742554812a40b144e15207500140050711000040098000d11101c0402070842500b50740d400381400b003501d01c2c181c8641c20301180b6a50030f1201501035100c030000141c1244882001c80c03501c04081c00c6d00c80d00c01e0000c070715800004601f500b0144280d580d1950070038000a0312900d800e014940120402009491501921f410740f07010a410f02c00034112240b04000019400411a440c695801d40240a0038100442004208503008500c4440140e0f8601218009400031a9800050000030150512107080031030004000030300c030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 30394582 1250 30393332 30393371
    0xc05010c08041106091e040608030d1d06091207080d091407061b0b090c0307080a06050a06050919020c12180904080301090c030906090501050601090905100b0903030904 74
    0x28403600fa00c0081d201054100a101d000740803c054000129500c60009514100c6000c000244054400510141c591142c0c3e411507000038048840e65880f04441c00145006100e148a001c81480150825007002c2c0c40d0242c903000c0182c2021542d40d00410300c003041c04a007400300c1d520b006514004000c92002c603d0410640319400c28004000c0c021403c2c00074074140181e85003100e1250001c200c00640641c0d66800e0180d840192040b8000d10901c0d008540a883c00c11081001e0441c40c00105040031442c80c4c45420756070002c200040031810000308003e60b459052200d90071420042480020b000201c1549000780200b50b4146010720800c21514000945a4020696845c0c81040240745408078418008840b2051b0b41c010440f08040004002500307055000024040c1a840c011410120382d07200c11061341e5018000340c03500d941d11420f004007581c2001269004208802003405103180000091800604900c40c09001040000c0d01d5140c03070b0380c1403003200d40c00314005100b0000895040110745010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 30395689 1107 30394582 30394591
    0x201081906030b010306271e0204020d02040320030a08130e01170c01140904020f040906030b0108070e0f0105010c05030c01050408090a0b070b010311010c05010c08 72
    0x409806000002c60003080745801950450401008803209100f40803003102c010203224070700c00039000c0072690a80c1c004003580d0340f000c03000020341e0308036007440002503002d40300281c1c240e0390306983d030b025205490056601e1416800300c01c00d41d00b8a00140c8140642c943e102c21188070001c0c1c01e14004149020717000c0b1400c1c484554a441c0f83d602d100c800c0c0c1041c000c2400215860b91002410010411822424a1b0000c2d085000c50700c480401d110381d00d0a58000c07034000800b50310b9094160100e60090000c00c5007000b07010b9582c1040b0b10590740c02e010f101d80070301485c80005001c046003001640101e02c0800b111506034030b410010743d0183d805080490729400148500020414203101e0980f1403402960303215940c0303d01a080110110301c58208681c4c00c8018041c03d00440d100e000581d040d61380c4108070200160071180181c036440c665100007000c0d90b00784a03043c0039540d03120010a029 = true := by decide +kernel

theorem cover : BRFrame.Cov 30215832 30395689 := by
  have h0 := BRFrame.cov_init 30215832
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30215832 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 30215832 ≤ n) (h2 : n < 30395689) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
