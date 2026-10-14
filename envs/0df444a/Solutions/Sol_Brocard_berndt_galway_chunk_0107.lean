-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0107
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:52:42.691867+00:00
-- url     : https://prove2.me/submissions/9d2ff567-623e-4ad5-a5b9-ce77845a02f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 19064754 ≤ n < 19244610 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 19066004 1250 19064754 19064767
    0x1030c03090204020d060e1003020f040e1c0f120209010f23040e010e0c07020901060f18060e040506010306120803062806020105090703020d0b040f0c091a091605 71
    0x1007600005921a0050015595a110b02c00705e50020031041c4504803821011030b003c151082c4040800800300c0750000d1450510312024001c000081c2556000c10b0060701c1142d800380740c000c100c140c402c1410341058441d03030080e4a4081e40900320901e10000c114143c1d20401240010ba07070403445900703a41d80e940c038106800420803e28034440b0303880c4c0d024444480304040b800060003c8500007841c143c0b0302040950703820340c80f0541d41c0c5003d8012020025800020700005000041c461101990720404614000041000a089810b400c9078241c10840000d0612101e1800714101409019080f0000f80b80820407285032240700e02144842100042800e83c00101168413a515054040b07002c0c20b80440c00b0070b8044090080741803641c510300c200c07000365092100040c0c1000c00450208100e0f82c0103005480410780030740e110000c4140c010011602c0039403807800d1030081020000340c0710142c0b1000000141e18240342e910041e4401e03801c00704610640104040000030400b46803078551202c1e00d424000d40307421 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 19067254 1250 19066004 19066007
    0x501030c12020a181512050106051204050a120302030403030e0d02030f0d0f020c06090d0e060d11071208060a170c0f0a030503070501020a03050c09100f050c070e0a0501080313030201030c 82
    0x103040d5005441c5101001202041c1c039015440c100c0c070b12070050b80f21b9040400400c103079142926000d02c1601c020030030501100c0e80c02c0c0c4030582d400d41e2240c030030b000307654560845940d102030741e80c1c00c0704412000a40c00b004020405400d4402c440314408d06500800000c45040384c000e56910a407200a2003099000c2100740b418000313034001c2c200c0c810043c001036448521310020240c0c0c4038001c541441e55031082030a40840b05000701c1440030700c04009010189800400d10001014000342c02081043c0e40c8204030082c08071301b2000c00d000601c811030783c5520f20f03800c0410810660065a410140b240701500d01a00303141c0c0ba000030075207081001541c0b401414400100016500300c0180d00c0900b0701d02002441204020066000f00703015013868a0420640e229001c088401c1c1c0076081c1c1043c1c1000c0002c1c2500d110600a0034000b0980c1c51511b4010300d0f2003074031040a400c082895001ea100e1200c070106204152101d1700a00b409003400f1401107080c04032844820480e8034a41c8800b81c1895036500965245a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 19068504 1250 19067254 19067267
    0xe0102011404050f16030804050f0a1206140c25030504030c0303020303010602012304060b0a0b0703020a02030c01030b0d08030717010806060a0e070e09090a0c030b100501030c12020a 80
    0x1840e0440060700a2805003825502da03e03000080701c0440c080d40c072201001400304080001600c0d000910142014181010b00403000720909000f030f4840e190540c00915803000565504411344181e17400724074402c0204000c001560080c0091203031090030b001e552503a07010400007040d104c0d000d006001d400e04503414155460310a9130405071800e00401008814075800200541c1240c2c1c15034002c01c40000080c080072016a2402d940205d084104000320380407030740f60b4001d02d5290000034102c00f2407583e5400c0010346980840e0b0201c015800030b00d4041d065250600c484e0020f100203090500249034400c001645c0102a0310000784843c5002c808030301c0580c46a4034801c04010301441142403941c40d4000d240d901c040803188644520315060000c1581411440c0040c0100c0c000d860700c0c400010b84800304031108200500c203d00a02c1018801d0002c6018070a281000f14003c0c81840d419003409420800000305941003541810300b400003a00742681d10260010740d1940c414401602d40d816500211000e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 19069754 1250 19068504 19068521
    0x14010c120f1d0d0e0a03080d050711030c0a02041104080303010608090a0b0703090b09150112020622030311060705030412021011040602010606030513020d020a09020d06170309030a02010e010201 85
    0x401c005242c80c44200301c002811000c00300d2113489082c0c0651060003080507010b92400b00038001d010a1110600085003a00705075001025420110b00c04010f200c001c51550b088510824103540c00722424405500b010b00c41d51812580010f0032614003400c0511075560b902c810712800f400c1203010000a50415410700c1a8214150720141d119082d0a29070b00007405401e140d40b003a140990850003103000c004000600c2c00042001c04d186410aa180124000500d19051070030798001400b080381d1030690002095068215101c0c1c030344810b80fa0308509006085040c040e07079080160f80040c0522202c203400006680e402507210104055110001400301c9c2009060703029000c0d500d0405549a0110034000058001d5545079030080040c070350b40b414100c041e58800e58601240e02440180300c005403c007590305212250000d041402c045035210b03480350407640503103c940e83d415034580e001d0040d103801007891540c1c1e0f400c0307000450510340900e000a886a55006009040c071007101c0e07810000f07074000e4000c450f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 19071004 1250 19069754 19069781
    0xe070909060b030105090c0315120c030a1419080403080d06090c030506130b0109050f01200a0302010b0a0303050307081005030706080f01060206010608040602030c12040501020714010c120f 83
    0x250a070b0301c0346209815082801031034410004a00050180c0900b2415031744202c0c80e0318014109061034030144000c03070440b1101034000e0f01860f03001103402c0d1002c026a040d01840b400d030461440e003103960703d1400c043e11162490460008240b1240200e4110b5050300d0503242c001450a6030341c0c0c00840950001c280d82d030f00510b545410102945451901540014818441650a190100030345e410100459440c5200c142c00303e41050310038001401c1c5583c2090200806052007059403015490501c3c00d6941140700d80d00d1a88504054420154280210410000155010703881c0d00c0c2180d03006000d902004010104010346540000e80b020305d190400700c02040e0140c15070f01c0203501c401c1d0041604204036120b142c00320303050000081c00e51000170100c6c100d420319914400541c40e00d69542c006540301520b80311015805000c4480410f8060b1a46ca00071403241000507542e58103440d103035002000f01e6242e54a02d03450b1814030840700e60480e404088030440b8000025180382c904001d40c00800420000c1c8c0c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 19072254 1250 19071004 19071011
    0xd050a02010204170609010b011809021602030106080604050c0a061209061b0509040501050d030905060a11160608070311030105060f040306060906170106080c0108070314040b01140102010501030c0e070909 90
    0xb5503c1002217806401101c00800a104c07100303214005440000da80d180040c0032079400082002a00e0740750b07024100f882c801401d10403880881d500004e0a40e02c172500800788a8015805110800c001000b01906951085e100818428a084e00c0607200d0703080400c0c07125032140c50318405020028258800d40d050600700801c411310700780c905001002d603041b02c00c82c180141d06d44400490685410000140c50716416a034070101e0314100000d10107140c000a03020020700c40d4000034441d02c000f05100080242040c07a20004441c1c1ca080030050050700d02400d440149840e0450031144285680122415140c00b82c8485654810901d40c440341d0748500d5001400d05441c0541c086050212034000004130b80031a100740902c0c022001c41c4500300c0c0c4140c4544842ca900c0440d4030b0030341d035014241c1c42c1d5000c4142e040001e140d9012804034001c0c090121407c03030782c4010300c030014070070088a40c1900740401740c01e2000300859070460b03907840c042101c5400b03a400006c02c080006203181d4410403904003e451460000d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 19073504 1250 19072254 19072289
    0x6010b04090e070b0f0723010903031d060601140d0e0a1a01080a02150405040903020a02010306060201060b031902090a03060f05010b09010e0906040209030102070311060705040303020d050a02010204 87
    0x15419400c1800340701509410850b124180c040001440d50945801c1203c02c0d00d007811180350140c2590100108980c03078030074042d0610080700040c0b03070140850051000820b030000b1074030300103081b9000c0e07000c0b202401c140d00f4601071080d00d00150b10b41c0d21540a09010003410011840a9403a0081d00185000107050104003140d088000c1107600c04a40301c0e900c2e5410700505a801052403c00074040c0d0103040d404010300c030000d480d01d5295004801c0d448141c03039207400c1c0c1b16804101510013120041c0c0140c0e1203288a40e0445d640340c41800010542c40c8000c01004c0d0800c1d8040e101e03840050064001030326180151340490400703034125800f0b100c00601c1e82c84d840d03a80e45441405001d0042000349094500000041d00507072400c102c9284a90503956028103034008010003400e000e029104c160026805d00403102c80c0c4e1401d03c01000e90500a03214851140c3d03200700c100b40b811340c00819140c10000d0900003000065000a0b070f0020071066814019101c10070140101e00a006075070000d91010b4119400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 19074754 1250 19073504 19073519
    0x1020c010e0a050706030903140304080f030a0b130203060d02090903090a03050d03050a1a10020a06110702030708010207030c0b071809050910150605160f0804050901060806031005090307050601 85
    0x340442103201d01d0684001c03650b85c19094046841004007e400304540c84640c00b4400400e40080d07074000d105080c0c5609050343c02500c0c80b49900215200d04002e03948a40d01e4601d0300d0124045840300002d55019440c61074000c0100c0d2a1541c1c50000902805c507070804034100d0802881030341d4a04801802680f24107a403810401d68400c8561284e030702092070b02020030003030b020900403030500071707015440e00c02108201814004000d00128902c3c0c1140204426a00011490b000e540100e41c40c841d4100e0322080310307004040c1050065880b1500682c41041302000198200c3c82c214070881d00300c4055040b564a400c0240c0300095038400c00301303003018070030000b03e20040e155104600400c0700d441100d0824000501c56412100d05a014600307140d03155208000b5548618018403c464030045048103001c510f545482c02a12401030480d005400485d00f0322650412120755401861589028511818620003080d00c940b03851086144584e210400507001110800c22610348503440404c07200c02d9a5501d81 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 19076004 1250 19074754 19074763
    0x41203030506100504080a0305030402041b030c14030f01050103020304020315090a210e100306080a2001090f0902070c03020d06050a051501020303010b2506060603180b07030e01020c010e 82
    0x301d05104010050490b00389520039410317102a070392014000c2605000a0300c003550305d600014822680240c030707044048004103d100d4401106509030b200403540e42280e0f1005004480c1440c1080180c00d005d0080081c008052200241101c0b400c0c01c0041c2c1d03944482c000b0071304084c4840c4610a540300e60303030140800b2000c00100300800c43d008000e101c008401c1440c5011217140b541030b106000405c04a02414140b4040022641003400c6050000c2c8140e0307030b102041d04140c030111081e07401d0a4844000311841c1010030480032010024a4002519810840e02401c0b086a5008040d00c1c9503002c14648100100201075401840c3c000300003008080262522034050b000440d201862a41002d02060b600404d403841c105c17030b21030144c002c0d40c2180e08080721032806400c45180804946040101044604254408070362210b0040b032005c2076240c141100641560480c0c4200c0020781c0c9805001c0700441d1001d0f2440e40c0040e4186004100343c0407072604140a400707041c1c0c1d900241d500e400960400e400002a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 19077254 1250 19076004 19076011
    0x12100f03080a080a020405030c040506040209040e03072d0807060902040501090e01060f1d0a14070c0501050106050304020604090b1504080f0c0405160c170d2702031c050412030305 79
    0x80e2103459540d6240342e01307001d90155100f00c0b600342c1e01480c84c0a12601c0c01d81c10007075019101400041c1001c6125000405031400a120a01d107a0000114002403208541c1c50b242482c6c2d140041d51981c507a034403085421aa48c080002d842d412000c280c01b0104190782c0c120500d80b6030020410b220380d5850380e803c0c10040040f804003003025842c20400050b202100801c05c1c08aa200101a404228409161034000788000342a801510380d146045d08926055075049070081400c1e5803403090075031503031800c03070308683e03040c0c0010b400d1200a00030000140d03a614102c0301034810103036011075510340900100d50b501030b10503080c4c10a120f0101d004620340c000020700100004a03602200d0140e5001d80520080340c0041e0340030150205158200c2d00c895000f51074a0000d24450450708030301488940c07041d2825000070100a8505480c0c1d00c1e0300c12015000c100c91141c1264000c10300203c1c062680c00a42d5445401e2010100c0020281d03019980c02d000e030080e10024421007502c80e44060403450020010b29044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 19078504 1250 19077254 19077257
    0x121103010e0a0c090e0601110307050a050a0203060a140106031a04050103050f0c04090c031103030403060c0f08011707060e0f040e010f060b1305091b07030801050a0501020a030512100f03080a 84
    0xc000852440c413910030142100c0818500390701d2911410011030302e009491203e00c038244002c100103800200300300003421583e405a805030120b40020310400d401c00700c02a105d04895810240c800005241c2d02003130904540007414006400e081039401030803008130240b4200d80c803030710380704c000800e002021604408444065003030f00c0201e0003410400003100e201c1131002e001c2402c1030310248000355411059403c85040107048a05003540c940e101402c2d19200d088620001d07494468405000e500886028091b040720403200c8440c25041c800180d50b081c00740309080402c200200d41c400107844402c40c200300c29030041c00601103100845440b034041c04d074000349841e54600d00940000d40c1030051040d90207a185004064030007174900010848614000f92248410b100c07c1d1000b80d19120100004103165807007912180610742c501401c01c41580030070f52125065400007074a08000a038410100c0e50b004032100101c211507100e1078505803811485401240380c4186140000c000e03c8050b02c041c25000c10700703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 19079754 1250 19078504 19078511
    0x9040f020103050703020c0a06020c0a05060c09040507080405100504020a080a08120105010528181401030b0303090a0e0903040909030203030108010e0a0803150f1302090405091606121103010e0a 85
    0x101e1308110700f244a0a01d05410301d82140d40d4120005050b42c0082080700700100c101e401d104120303101c0c1e5040500c01c0c0c032241c02c036150001c0c3c41c490034180350194603030201c07407400e0965440c60b1649449840f40c00303a241480d0625a20800101103507500c2845101600f0010300b120840801c1e450401c40f160700c00360800760410306407000007940b5807107202200c2500180c03d400043c0d11031600c12410030907203c00e91610a1000100c00403029842030a031840003018005d4906c0c40c0e101c0d00c1800035044403200010140243c00801242c10662202e00741101115000d0202c240f00c1d5072002d4003942180a15000881810b01708194202490341c008080c0d410385203800020804980044401540ca69515600820710b903000e00010702035400781000714202c0c28001e03181c031102006423000034586070f8034070b41070061039540800c030728405050600c0740552007809200100691003a032034000e8100c8556200799020814045a807404000c00c5030040000c85c402d2040389500c95031288101080f900c000c44100a44914 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 19081004 1250 19079754 19079761
    0x30c07050306061c03030204090507050a031422060902030105040b0103020a060503070c03050a0507120305090c010801050d06051b07030c1106190806012a02010915021203060f09040f02010305 84
    0x1804540c0a00070000142583c4a5250304e5066107411620584207806241d0300340130015003a00a07000d00c0340f0a58003079031110b075542005007002c1e0032191841c289945003031210302041524601c503917000003414480c2d0002c62140a0070301d00380300905107001d4029015400d0105100c208006100044d069038421505c075224903440320310071170b49030200700c406400003070381c142184001ca40200024011811149400b0749440b1250703c400100402684d810702c002a550360030007040311400d10004031980400d01e0403191951402e000104440c50380000034011641e02c070082046103a0000485051200400700030380c9501c110b0401900c0052a50b030196500c00c05000480b0f038514008040b141c0e0700351807040c00e1000d1940c44808540c10f11005051743d040c0710000518005441030003c10010220707020380c0d00c0c8020030741403000402c840a030f80d11081c1c1c180101501e030004a07402040c020030b00c220b00e070000ca4490703442000080f01d0000b1211031070340001015092000b4880c0b40200c004491f4000c1e03c0c00d221986 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 19082254 1250 19081004 19081009
    0x7090209030111070b0a0504061803020a121407060209030a1a0603060609040302031b0c12010b040b0d080d090317010303030209010f0801121b0e010b0c010f0902060301030b04020a0e0108030c0705 86
    0x464144c00901668070800020040e400c9039001c1d03034015000e514002405454130390188901c0d040c07040c0503005607110b0048002007124011091440448034903018449911030b6109110a01030540010520754000c15030142d075460401c408030100e80c001850440c6030000000310a060380b030a031209402401135100145003801c0400c1c4040c02503605900542c41c0500e4102e01030704000003500300d030b42035000c0ca0200b031802ea41c40c1d0031420880c03641c0c0303800015041005002c02c811641c906c00324900400c812080c0601083c0746805451800c10369020200b4001045e02d0102d4848540304035035490070100f40004424981d05502500000c0c6081e241c1a1691418500650390400c09224201c00d0104000c80c410000e860040c2444031110340e0300d44000034540740e60507031a000f0340903002040740e06008165210003120900038049844a052010001092150086aa44c1c4414000a004042d250b0042403c540310307220148001c10000c45040383c2942c4903801c0c079841c0c1e4400c010100040c420450040b0340c07032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 19083504 1250 19082254 19082257
    0x41214010209090a0b01030603080d1401120201170702010f021b0c010801050a060518030109050105060901170601090e0f010606051e0f0304030c080d060305031b06090618070807090209030111 84
    0x2e401041c021044e030315216140090302c0c50f820418100741e00c80100100048000b0040c000390000d48101081d00d80b0750200341c440120b416844100f2009000d007a0748050b0340c0000801c1c030703015a02045010b481d42c070351390280c0c0903094500c60603022910000c0d00c6a00b0b00709141c10460303414904c0b0165034442011400468000d0005e000304c9900401000040150f580150020a000e2490400c0c0403c05000000080d0843d101c08400351856515601003190a02e0540150b601418601c900400d0058400322610790301c40050040d40c500940e9507802200868042209002c2c12240c80020b124554858000030560f03003001611000c88020021075100801c4a1001c0d0b40d128198030760514210742c0c95840403139009405407810f9a05074010043c415405583d8010301000d54003070310007182d40701c915000c214882d00c3c900c074114120f034200f5018002044400311314a5042001458110180210a00003d0070444d096001103400d2081010000e0030403032a4000e400c810600710000c0200301c0e1390200903100c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 19084754 1250 19083504 19083517
    0x3030a0e0d021b04090209010e010305010c020f0d081905040510050a0207020105030604020d0e0a0b15010c050604021201020f0a1e0e0102070603050a1b0c060524150c030412140102 79
    0x50f0700015446060346140846a036109140280041080318140e0049460070000b078101c1022008014014400d001c3c1c02d0083d00022078a902c01055298500f4102310b481e202e603280740d9800c01a6000110b24410f00c130144041400441a004220070b00b41844c282e556214690b1a4074105420300c0c000500103611407003590710700358040c2c54261860b40c03074104003c02507200c0706000030310541e20102400a560100800b03c0940d114140b050b40030b0030105070010070710300740038600e0303041103441c840120004801096990700190b0540b528003060100c114864068041d4510540034900c4c041075125216902c074610086025500d0398018801c0b0322844c0403903510300d0743c1b6045809070303200820410441d84a90300c104d91103001402d0010369040d43d000d018041c221400c2c00c0200150900c50801c090040301d11641e07411030f1030f1469001c5c0181c1400800030145900341e4419100b078200302041181480312004550280010030300f5260340380c0d21107201c003006c0e801d0300105442803140002c0d940e9501c9014400c9401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 19086004 1250 19084754 19084757
    0x4030906090f0902090316030302030a120b0f040b030c0402030a0c0905040207030e150c01060902030402120105010501020705010f05040f060503090607030e0a0f050307051605040e07050603040b0405150903030a0e0d 94
    0xc2c5007040e103150041e5000d60841c58040c411004030b85070074000c1d21980c60140d03102c1da010395907489900000500c0403004442c061202440e0008000465903046d4081e08140000e44003c43e0790b146240000c0e0410007442d00d01c0340c0050000041140401c516409580590302035218500c05945840c2400224018110000c020503004201c94805161a41d04541c07103810121801d40307408103540c2c007a03007901c0300c07a400f50b050a600441403004500e0680b500742c1600700e103100204015850040001d54603c054401d1702d061010b41810f00c3c080700e11800440f409040c03034500802140b41e03030305d4000702598021909505540a004003080c0754a101340a0400902620002000d00704520b4036446d44002d040f24044460303100030024003000500c00c7c401c51443c05948406419024a0203041c00305643d0185442000c540100b5000d001075a254420349070440d4100c820b4109542d80c91800c180f6180340c048045003410046000c00c480300c44000000c511510007104184011001c2c0740c5616035808000440b0380 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 19087254 1250 19086004 19086029
    0x3060307060305040212030a03060f060509010804030e01050c19021c0f150f1e0b0402090d0b0604020f070501050402030d08150d03021f060305160b0f0307051b01050403090609 77
    0x4038511070f40000b0303085130009003a0f4030035802c41c0c03420500d917a00c2001e00101094480720100031040040e40c460700240503e040c8189003000c0d100000f040140b00a02c02014490607040e42441e6902c42c00640e00c801c0c03903480850b24000d141405e01078000c8980c1104034441e000b09080c498082542c0909d615005a1028041c0300300921076440404d064240004248820b90b1116940c404000502441c9140c246025041409e6641c0003002c10a80307080c010b8890045004205540ca82d03103907041c0d072002050f080b00d105e1000780c90307400005e00a8030a000401c08103c8010075502c0038020190b1016016510840c00c5811822081105841014044503100c1c0310070510030b2021030a0a00310302c20030107070788248140c81403404060580348562000c000030001250b50b03103409000700301c000c21410300d4000c0740d1041d80c0780703c3d8500410980e103403090101c42c043c0050081b0215141601500945800c81d2458861200b4641c2010005008060440703068000640e2804000b6660f40505044010f5404264414 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 19088504 1250 19087254 19087259
    0x804030803090c06040e04030806090903040b07060609050c030a0b030d050d0c090504050702071a120408160519120306030b06010c02030f0f06010303020609010b06090411070611090102011103060307 87
    0x503610707080103104401030b009181503210b2999550006002410407a00940390074246030034028280c00009281d24040c1c0c803500e040c00001000003064504840d45010b40700da48044924142000d800a0340c0099800ea0901086c0b0460000e480c002e1031207444075210412a0351060000c15a8801514600c1c00104a080002c2850450540c02500e051429402c21003045917842000c1011030750225000700040e00400800d00a1118401210305d6039407004c0079450500d040c01c12660030142c80a4001404c441000070710250a40c04109030105098001d0241c440e01c80070f0712040002c0a0551070102c400d41032124805204034081d110301029a9000500308900e50740300c1d0015600c44a07492420fa03454450f04d685204c07a44e104103e1440480c40788800f0702020f51643c03401074a40903000d455681c182e41400e1116407652a100c05039000309408840200e8502c400c0ca207005c41d9131007068005002c16041801010000444200401390030f0801e0b8000c204071000400100322500007075400a40c95040000c08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 19089754 1250 19088504 19088513
    0x50901090b0609100203090f0102010203011d06120706120b19051309021302070203070f1202190810060608010819080309070b0c0109110a06050a0807120e0309030d0507080403 77
    0x24411440080c2003a481d251401c0000740440d0f000d0345030840140c0c0300203071442c7c46007020285581420400e000940c1154100900242d03440e942c0c00300c958020f442080007500c981e486080a000505440b0280d4000980700c0d6801002c0706c03121a00010440d003007100c01c801a050040307611301c04052254480c48000d00341801c2021885802c00074112040e02c4030044005640d40e040000c0b089810300a005a80341407502c185800c000150340800c000e844d04000c10000d503e041066864865412aa2220104d0440c440f4001d03801d101e030003455441c40341c0c0d02c2c4011006c0c0c09600c02c000b6606261503503406682e80d240343c96940e00001030801d07401c40c0b099003810f00141051003d1a00030310000103440300c058031400c00d40720a40055001e1403641e91244954410321058018001080b60180c0b40280c440d810030034090316510881c80951f0810a1800c00109100c1c0f02d044900480061608113110008080541e00d94940243c10034a109004104958101a02400468010300e611269080c10b01d89140c85 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 19091004 1250 19089754 19089761
    0x306080705101d01090503030a0201050609011406040911040f03030c03080c0c030a0c08070209040b0a0c05070f0f0507030b100602101a06070503041208030405190309090b010e09090d021605090109 86
    0xd2034140700c0d41e030038081002e550070b201a042490003603000181c1460410104803b4910607440303049510311200011211380c03100d1003100d054900c8064042000c6805010200e400d1155a00c44c0011030708560000c810568400009a50341f1300a6503410301c0d40d1075030400414248250031050040398000c006005040b4001d034501001a03000301100f07030400c10341f81c01040b02044100c90841e481048079007003041d440391500c54000117050518001d03040000f140e40d400340d02819620007030321442c41c484840c000c21604004110203590310002202450801200f13042884070107010706000350040f48010110000c00d03114204400000b0b80b552110b07004640140f00950380869001e4406020400c03001c500102c42001d0b250f04607120310313480c42d586d1906d81489802d0106051500303881072500660200482e5003d1100410740740d858500040b40707070340c1c04010b03103c0301d001001040d0491094005c10141c08401300e540700000da45070f02529030b01c038041500004480d40328015141e2000d02c810061100500652 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 19092254 1250 19091004 19091057
    0x1f1b03030207080301060206090f0f030304020d020418060f0f050c031314010507360506030702011404050a0303050601050a02060c09012106050112020c120c01020f0406030608070510 80
    0xc0042c42c1c80c0a90310b40c07445960090b000350001d42d000e0710a010028004019075a49c0101d602c014000c42c0c07240708212038991002400103481034a00b18807150940d9120361014451440c40c0020906800651a00c040540f140803104042c0902d071216002c005032149c01441d11800c500c804e041e2540e603070900c01c00d1400d14695400c0d0327004440307a40c132107440140901c10203010760034989034801121102030f0204010455072640c44c4c400643c000f0414201c0858403181010b40e54101c650a880e50b459500480c010300e20b2408089420a60000b40018024045400b44101d8006e0750305000315903030a0015101c80c41415040c1006034003c0c0c00142c031407502c070707005024a07840514000801d0060151811046e411343c00040c500c0c40d0303503080200640c0da00034100044a25040074154100803442c001d8030b8030f4070f044400200e014080003614101c907560a60448005162420446464540307070400280248524092a0841d10070684003042c0703440c20300c00081d1024a60b503180c80300c20140c1031004640e1840d0748c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 19093504 1250 19092254 19092257
    0xe0a020a0e040f1b03170406050a23070c050406090207050a03110c0909030d0b0108010b0901050f070803040f030201050a11070318030b07030b03060112050307020616050712021f1b03 80
    0xa19040c0c0000d00100701013001544a007418500c180c1541404c0790f0b0410192050f40704544100001c000c1140c010301903e0781090103003440c05d64085107408024007955940c00e5684007650002d01d07d020000301e141850305480f001d0720200582a1601091003c912035030038054004d40c040c0358a0000640306110220904008205480e000c030031402c046506000c09442441d125080030900c1c2c4642c4910b485000100c9000746025115945000b100d28624490b6881e8103042207030000d40303500050400c2d42141c200943c08110555030386424209400114909035080f0019406c00d008074a0341003581c050045088181e00c1104c1c60f00410b03076416141081050045040f0301045203000001c5a41c3d80032840c406c0c1116140450414103901c00c150a01d81d050704010300e400340065000d004039000006441d103080c1e040c0d84491792005d00c2d100b200c0c8181003540006206100b00540410998a00030070340045034400c1d03410000d030000c0c84210703000fa100344040c9000040c4406000d610350349207034981c4102171f074000e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 19094754 1250 19093504 19093523
    0x921010204080d0c1401050f0109091a0406060602070602060c0d0b04090609080d0b0105040b0a08180d030b04060501050306090403080c0f070c0311090702030412080c010504030f030e0a020a0e04 85
    0x50b407004500740718014480001007900e882c400424004100c1c100600c0c12034920080003146041c1e081030040303000601440c031006030340702d10910400160b0f80050b98090716400454040385042d28017203016250a010300e00c010b01440070005001c4d070000a466003e031809020b294148201c0750315541c01480702c040682c1e1301c2a104c12080f000320310288228a00399004080190341c640750309020030f041d110404d280c18100042000100080500c550640b0400031562400803225240c040080107105481025180d09001d540880c5a980703400d940308403071000d800c2d20305100c0d843d0b50303000550b042d00046a41942013030030b120029000a1182030b03d030303a012490040707103030034420300c080380caa56a0400380d022203405866400500c28030000003da03808d00c400880d00382c2c1032031603c1340009440303001314898550035405196600c41080000403d854540c0340e810003c000740c1c81c1500307005102841820004000c03c1c90a94100303c158400301d050801c45401034029003070281303080b0840300d040d04020820340b80c2c83d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 19096004 1250 19094754 19094759
    0xc060f14040308090607151a0f0303071401060506130f090905030702010f0909020c0f060901020f040e22060203180c0a1208040f031208070f0c030c03091a04030c05060921010204 78
    0x80b00e4203903c0c0f2a2001e1f00c00181c03082c2c3c0719409050708054894a0340f00e490780942c1c926007644c001044a4503640e00140c110050440421083c1c0509a260040b5038441408a281142d8240c100c00b15412528420900050305a480891008540e40a14040d1282c5c10811042015500407c00052110110f103051881c1a940300c07a03074000ca07000980300c004135400150341c50184100c10404240c002a246000b1440c00d608107110742d02501ca20300c01d86d501101c1040004594001240d80e4900d1071141003c0041208510302d04800254003c85d48804000101150350801047c005038008104c04007038204423815040040341045950803c004603800041000041007000034a140b860040d44102c0000d801d2840016010f4010070005042c00c0420130300c0c030048524254001241101da641500707004000d10000d0a0495203088280c1000f003121002810401016910b00d0041080300c2c05840b003400d2141d190410084184210b040180e48482400451000c0954018884d501a4003500c001482c055 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 19097254 1250 19096004 19096013
    0x151e12150b040602010c03060f0e130f02030d05030402041506050d0b060714010e1002070c060e030a0203010507020f0c03030c03091207090501080c04110702150307021006030c060f14040308090607 86
    0x10b005800c03550043c0d46440e1403109094245c080c0c100581460a500c29046003402090408860010040010049111f5807202030000e03283c2c0b0844141e80103410b40710907801c028405004c55000b50b0b000ca003c0e074038081503050000c1d2010200310555035a0f5550b5480c0610b0102c0700f4010703010386100360781e00c58400c2041b8000a124034401038810840c4030000314283c2d1a02c0482d5041600c1c00d00f088100381e004103d00c41c00100f1010b4104143c68040c14001c12030500c0798080b038a09500000700a41662038007091050350340d00000d50642e0b8034070031001c0319545141102070503241c1c00740302524019540180316240383d070324181b1400580290040d0071600382e240e4402c10082558801c4e4400c5501da001117003141031b141130500840c400341c2c51000803145428650760208841c0300e04880700b8040910040042091984240014449002c0040c01400340326264140401c114000d4032840001c01c20a40038010040c0c09070988027135004a2944007403d241c0756450350041607121064056000f82c08005000016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 19098504 1250 19097254 19097257
    0x905060409050f07020703120f030212270a03080a05040f05060c03060a050414040219080a080c0f070e040b10030b071806021c12090606151e12150b 65
    0x1009510720100315402d055072100210740014100c030003190404401840441c040c0c1001d2142e05040e4540114030000418048000f030003207445403c0e99140c0082400800000b000c3c00004051010062042e181c0c4180d1440743d0340c0c0490880107000ca0180310010354180c0d9144c1c4000da21034060840d4103802c002560b1202c0c14803d00b1141d1218511011040c8072003410444107001c090202640c0c00c0007004201d101c4856402d10042c8001c0c0300326132a02c0401222407904515500406241d000c42c1e4541415107000102c3da00410300c02103207031240c0c02c40c8104d400340000c1c030030040f04d49045020025132100d8644106091000b01091b09140b030740340b00080010503420009100f52030f196208503c148002d20385e948240703c1a8800d10446d80100603a01c18034105e01c0c002254003105052001e401c60701d080618003d0a20b525010b80076614026000030010b41070b040d03814070352110b5a10b1104a018030f0340e0007800940c00c15195000030b05080c01e4111300305517580c400c41b08000076a15860007140e944200180d07a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 19099754 1250 19098504 19098509
    0x60406120503180d0b0406050604060f060e180402060708031b040f0e0a09030815030703060c080403090b0301030b01030602030414010515011101060806061005040e0f01030c08030c060604050709050604 88
    0x182d100003180000403c407004500400c4004856400e944201520342c03805484000d040a09171035903544c0490455642ca80c0208002c042e10948141d44580e034410107401c050819542600603804903402e940184e90401140d84a40d5008282500b80034260300c0d800a0340d00028039601d9601c003180e50104203011124081c000403c1030440120450f4204401c0c03c4640368041c0c184450903050008000000e9042055941d0041f5079181d501c0080280b000042c0c030f003c03216480540218038000c29600165801030322144030f10f0003911034080f4560340d424981e046100922020b002314003142c0043c00000c45c1c03a001140c21a0181b10044400c100d280390f002e085500039500c510444071005840300e015604a11028030a50010000700001450006c219440e00c01c0205590310071503481d06582c0d034690003842507070060140a012481e4610707040c03030040c0d40b041080c001030361800c2244c00f0005104000100720b45240394000060180c1d505c640c0c080c000a00400740c8076000384000160701068586954016000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 19101004 1250 19099754 19099763
    0x20c030d0c1404120c2309090c0a03050105010801060b1206090403110d030501050f03030a0e0f010302041e03020f0603040305070201030e031c0212060102060103050303010b0715020c0f07080102090d060506040612 93
    0x5034034000e01c5c002c45140c80d143d00c212a003c20300b054807002c041c50010b01000b10201521000b845556000c2c415042030309a41c88182d0003c42d02c0c1c00442400015403000303042c1d440300c0000700300c130a45820300e04501d8080c0600120808030300c000026901e0a10300d10268105100e820544007000c0540e060508000788039000000082d80d88004201c9498803405000e050402070b8083c514100c01d404008000b110b21004460060314003410500b003a0b4030076030482e1300402029802c010400720411803a0b0802440d44001d0b0b1050b10207100c030504520f01201140e014030780c1500c89a191200b154015030150a5001c1030410130b0106011540c100c043c1010791a40000c0030020060340d03454138800c40c20401101921103411903120b40010300000b84004112815144106c240036180c0007245042c1c6201c004a08400e4042030000c1800c144403140081e40750404440c201c155501039031100c0f4601e00300d028a41d402036000104000b04404038003190320603500411b001d8000f0034002d448050301007041c00090011207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 19102254 1250 19101004 19101029
    0x20705030c160503030a03020c0f010501030b040b060103020424020a080310030c0807080c010c080d0908040312030b03030301180e0d0e09011512020c01091a011503020c030d0c1404 79
    0x5081520a0100a80700034040c0c4240c2c05207801c29010950702e0045803000418103600041c074a41c8000704101042120300d1003002400300c0d44c0c4030718080c1d550000c01d4404036000440c00b000726156601034001d44082d140e248888500c011030084618a45000319020794040d4010160280c011400000043d8460f045110741c2d25003031403451400e111302c40c280e580001da140c0c000e0441407105407030210741246421401d00e00399100403480d00b0043d840b48210300d0007a50940c80c0c165008100310740786000e403045900916031030b100d85001040a6042d6109201c4084d81904100010300080082441e50b09007182c44002c00524003241d035803c0d501e0082046800b4006c50b24514081c6c0151500c500728a015003040d18001c9106001c0c070401800c102c0d44992070300d0400da00411b4400740202c095000b8910250810300484240d02c83d07074000070f2002020300800c9881c00789007081d00d117070074001c1c02110080c9040c980298a050f405101e10002030071403524100800c4100c14421840030180700241000d410580e4860 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 19103504 1250 19102254 19102267
    0x60a080c2a0d1b06020906041520010e06011a040e1306180503030705090f030d0f0810050a0b0a2c01020601060e0f10090801020d0e0f16180f02070503 66
    0x11450b08919803000c508002101810442200c1d0307000030035181a40c4103201503159410038000a0440c055600003503040000000240703203d42d8400c02140307550408103a12400c0a031495030b160309130f94844c8018941680014010008841c8000041440440c0b5101d110b050944805245103c1e4100341c0b044e0f02e8503c180e840000510500d88280e030751052592a80c02c481c4000d659580c0e1326400018914810300101080003505502c0d000400904100b0017010349816039000e5102600d0303034000e032840c0c00c0082e40070b400007003c0c3c10b143c00980059500003040c002019290036942c403400c3d0702c80c2d1204000c120840d54617403944d6044441c3c056042d0031801c003003684540381070002440c081c0305034418020010640d010072143e455400039031299040075203a14010401c90301059034020100c0d44685215031000a80843c0d5410643c01101425900c0b42500e001c1c01074003040a583d113110720030044107800404410400f03000c1c0c4004d1110380b41211600452000400d0340c041c0101d8010a400f5901ea40000982 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 19104754 1250 19103504 19103587
    0x1021303140c09090d0804080403020d1a0a0c050d020d0e06010305060f070e0108070c03020a0b0a0212060612070809070503031605010c0306080316030912140d050306060a080c 77
    0x70b014042c00c20b80d825a010314243e0310003581c80c2c040d1a1210103000d12500458140410441150041d5401400c0e01600344110b1508200b01c0c10551900911402c0d4800420a090f0b040c0c01982c02d500d80580c1d803a81052000c1d034807903000398091107a203003041e541e400010316101c0c070611205008500600240001e441d20030510002120010020b204200b030603003540145a8100140c50340107441413030180703100c5c5518a0113070f2070880a860003030700f400c50380f800308081d080703954005040e0075402003000750a81d12050240300c03044c00707550f40d482844c0d078480c000280c10364864134466a00c20320802c2126001c40c1d03142c002c241140d00181e1407403074210101c0c6001d02404402d0240d9032821109140c20003400785020039190b02c900548100e5124181800181c00505101d21220009401c07246045a5003041d0b52410040010304019110414041c02070b108040b540a0016207206441c00340100f49009980141200d050000402401c8243c0050100522843e00e00c0740c400c81041a02000b070591000c034040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 19106004 1250 19104754 19104763
    0x90302011b0306151116080303150301020f03040605100321090e040507031401020d02031006030501050d030509090703020705030d060801060506090d08031503030c0c0103050601031112090102130314 87
    0x2401d0301810b0400c03404200e518040304d0032400c141c400d441d095000585e4044014101090b1420200020541040116004c000400154003520400358000b0f4408040010300d07081c0d016440c1124041c0d00f0074000074004c2015600326503030080e0b029694200076a129034031920800300600480c0000141c0251200003140c201406c1000fa15415000b031001cac3c9415a0b9465440042e404010401e49245001c81280f200035010303102e43c2d401c188425512403801d92500b070b03000e8406101362000a81404000125410980d1030050001e0b056540c1e9858804102c09000b6011303c0a40742e081015801c007d03010101c4d40030300280c607052030700c413101040991800b01e20601b0340713055412151051100300103e8000780d0f610150441c3d20340c1e200100319100c0da1220111004c00c1e1045040c2601800002610305111001150000c0101c0742620100502e40742c110044040fa8a410b80c0003a00d04001c0064800c040e040c8103010340c1c801e80c140c002500d4600a1780c0d1a810400c00341e4400c4501c1c298400c030b100c8510381c0920 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 19107254 1250 19106004 19106051
    0x5011403040203061302030106090603150c050406020601060e0d0c060e090f090307030c06060b030408030901050708060a0302010305041b180f0203160f0909110315030a03020705040b010c02030109030201 89
    0x66500c0c00d40c103190300020b480d070901a000150f034a100c4180e120031034400703401c04401030650003010414581d0300d050400d121640c410034030414600c0c1c445034940e071600803801d480070b03601c140d40140490780c2000d0b02036926207650ba21907035004810b41c82c000001819800403501600c031540e101120041c08a05102580c100600a0301c0e401c440c2004005101c50000282c5001c60b4061074080d400c910701d030500000a03d40340e008041200000401c00007440b4201006501400c81c4000801071591000300440e8000025202658404414038080003d503100e9008540c12500484903ca000c0c10f0760100340c110080c880c5d0001c000e1a49601000241003e00d03c03582d00d40d403890810541c650324168a08002e603c00914a003001d0001043c406426184102e0348000078060040c0104001114400411240c4d001260b08403190b03100b42d5400000b03828003181200d140e80d0301d074004001d05810f07c000c11000e020711180c8a8100800e0303030350220144c2d4003402015220b41c000d80000a01c2c0c051044810040000c19 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 19108504 1250 19107254 19107287
    0x16050a031e0b12010606022a120c1e011e17040311070b040b1b1e01060f080f060403030e0a060207080307021203040c03030807030e0a1208090a0b010e0619030b010501 73
    0x10408101c400c2d00850001c11400307032050381112241500b08d202070320381000d8901c80d070817104501c001c07030300d225000442148200040716150190300815445248001000b094a4005481d052012003101c050300038007080d0021500b400003e5040180c0b050603000b504840903000140e07402c000581801007806140b0280400c100c120303190a00b4204140a01c1c8514409038100039200c400d6603044e500184541d401148401ca01542d1300301c00c06580c940a012280914090703e40c05000000c2c940000007400c081e180351086c050161a596628150002c089950040906002d941043c100054052004118440c030451400c0d441e802d0540000b45081184803050700703503020420038840440c1640c04800d007100c0e410303d05030700942e4501c241203029009801c401502d41c41900c844c24100440c0c0764070110750003929134680401d40c1e940c80c1e0041ea145011781c400b07403c04800e40014440c5100d22308040750302110281404005e000f880030f13080741500040d8010340d0420500401403007990f030f100515010a2200c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 19109754 1250 19108504 19108511
    0xb0a14150a08030a1d0415090b13020a0f0c030e030d0210050708071b050102040f0e0403080a1a0d020607080a050315010c11011b060f020705011416050a031e0b1201 72
    0x1400c00070702900012910302c5c03004850240240c400c0d03640c6800044034011344500c07c2a01d1555126000007501150700c1c41c521402800c50501c0702500c0f00d1095896107180c5035039031070101c5001c03c0240c6001d0f4900c0713030581c10400740101804158604124407138064040794018010780003501180c0003291b802500d002c04100102040c06661948403101c000b4001081102681c4000c061074054024466076000c03580114103403800181c42d080301e584181c4550302070345400440c0c0e9039600d014411200c0b070301d0b04090212a030450048150500c800e00d494030a10240030186020500e8642c207015400c65a040b40015070000304100303004500e940440d941d9070003030820100307803140d50341c07510240d500200c4000d04000001c9180e440582115100720303080354000c84108401c0c8103540c00c03100030f0750080e401030f02e256003419500c4107800c40402e982c80c030600d80d1a807141c00081c1c1c040b40480707065200030010010541ca451000b5034038000f8202d000f02603019200001283e40c040c0302840b00c0c2442d0612460301c2d5924 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 19111004 1250 19109754 19109767
    0x60405010b040303051809100302030c0307030b0109020c010204050409060516020307030903030f120c030c0f1812020315010f18020c060604050c040305060c030a060806040c030b0a14150a0803 84
    0x40001c291802c0d01d03418106130b5154100088518142c81d014900d8a60001e0380300c003403200700760f4031032048001d803070081d029030704100c0803081410396030705071440010816015031004100320711040d2b002e403040c8000000058030701079441e0b000505603a00d2107004d60301e6990312814860301d0040380c08981c0480c0a5030020b181015143c0d103011704076080320f10002d0240005030021040342440b0f40261101111142e40401c80780c05007841c01802451015002070100d00c040700c811400c14021405414245480b615005144e81003c1203000e0380c0c41103d00c00c0741c061040d6001e00240b51440c1842c03178082c220a28001060a203880703050201c2070b0240c2254020030b441040b1030000d0704030100da1542e20010656001c1000c0e11070702481281407041c2c3e840640613004000c140004103c14a0007180585000d0000303201c9651600d00c240d882e01400d4070020000111203404100003001d4001c0e10340e10076988140003c00034003000080d80542003c5603082c400c07040103032810b4034034075202820102400303a0384011400e104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 19112254 1250 19111004 19111019
    0x3030403030209010c050a050d0807050408100b040207141b010302030c0306360a06090605061617040b090103050c13030206030402120f100e011a091305071202030606040501 76
    0x100240016040540010740d00f00ca50b4084c40c10940150f900c60112942c08529050003a12510a0f020300e40004480d2004070300030030700c95002d85040d102d601000d891100f824204040040944412807500030b030302440f0761008101c1d035980340000c00d18428050b004112082c5165061908212001070501d881481440131101e212401c1e00c0d407207481a00e40003213549802da1280c0307000d07480000443c0c4852403080540c030710342688000c85000d1087c000c8240304180d1a80400019141103009154200e0400e00180721841105032080380740070b000f50400d03004840400050009580540c0003580403000001b80f0141030359040c450140e000708649030071801e1006c4001e4041c0d44031140d210103481004048089002c1d0354800c2d040003098900201283e91101c1801d00302616003004401c00c011181c07a06200403001c40b81802441888107031001030303945401d91842041b54818005e044041d0000d4403071a1031000980130814000500411003031140c540c0d946104240c03070044010129405181804010441c40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 19113504 1250 19112254 19112257
    0x10608010510030b0301020c03090108090606220213030809010210050c030a0c0203390105041e1a0108030301050406080a0b01030f05030c0d0804060f0218100507060218030105060a0803 81
    0x1a0000ca40400b84108490300c00c90240014540c826455440052070203460000040203140070345081c2c072801881c0c1c0c0c801213600e0700c3d80d200b1078000340c2241030b070b403010421041c201e145500c41c8a0900c07001400e01080340000b480f88140e40e00308a800e4031002910380695a0100004050038495400078007952800010300c02c51400701800d41050152248105107246009100ba500080328142071000042400c194080403509040d05031210307681601100c0b1414501030080e82e10841d0020140d1030500566440c0b0415140418402d45515007a00c1c01c190000c403402003050700900e00c40008503244e5062404000c1240d0055010384400e80c805130341080060071b05059503046940005004d8044155401c18074110f11a941450090340101110904030603004a0f4241c0154014a010898801610301c248201d10800419020680260081703810600d00b0208800c09824503240a9080c8240b50b40d5141c180c0c1c100000011030201c9603001400d1505003442050f0384640100c1301c102000e482c02c0581902ca = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 19114754 1250 19113504 19113509
    0x20712030b0103060506070c05180906010e0402011707020d02100b0114090d1e03020105060621060102030d06090203090d090b0a03090503090603040b1005010e031e070503010903020d02070e01060801 87
    0x140350315801007091a80c0030381e000e00c00400000d00025a5040c0c0c0d450242c0c040503090042070320800f90004081078582010560398851903042000741081e90030315811654050300144128100b003410061240303041007100b03413030b40504001c0c1c00600c4000c1030b050020f0304051801010144580c039041d50b0901582e03000700c500340300c00070346488150f482025a0116903514400540a040038498000010f200c1031510401c0e99424002e900800064666104208481c42005920541490f14054408072601c880c600c4a41040050045a2502e01d200c0810401d44a541c1d00140d103055010042000411040c4595a9005403502d0081d950310b04000c0e804049000d402c205100301962040d078442080010022102400b000504071303522480c0c140b07810001c92400302c5189842d80c154480019540d4040c161070b00c00d0700c00007000742c030120110100d440e2030b4035018818418a4030400b0000159a00e0a126015606000364080c4c002c10100d610042d2a06540b54030542141c0081001002150791081d0081e05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 19116004 1250 19114754 19114757
    0x60a030b09031b100b0603060a06050c0c270f070504060c0305040f14130915090302160605041a0a0c170903100605120309130e240a0b0301020712 64
    0x11688480312114a140222074880b0b0f41c064101100c00104030000130802048a6420424440b0340454002d10000740820385401350442151802803000501a0001d44203a54400741140c110f00c03401800030b219041100b410310b00c1644240310505002081f84000c9900c011261205079840c10403890090491065204007400c000f0382003040d5007058820000c0303900814020b604114503d0b21440d032a050321001e107107000e100700107501000c40287c400d40a03103044960024242c035207850805000201402070880e00f1400c6000e801000100e030007640013400090541695016261804c007122020358802d0802c1c005480302c028004950080d521075200701300c5550103007500f10b0380c924076400b00059004200c103050b414012080c1c01d50000e0744030350101046810403209406003c0007002c5103902c912802c0e1125070051b07400c560000c00d5012503001080c50344901e0003290307520305c0c80000c1c0100b0070300e000d90810340d004c100c0e5060050f06540740c007840300c2c400c004900031480d00140c0d50b03444600e801005100e20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 19117254 1250 19116004 19116023
    0x20904081309050106030c110706050a030902060f09030c0109080613080f0c010c03060501090b03010e0907050d030507050d091212020c0a0305070509090102030106050f0705070b0a080403090e060a03 87
    0x4040100450640360000003044007006603640b00e15a92000e007900b4040c0d107002a2410540e21003c13032046407001d0171100710344050520641400700454140e40320317440c8101456110309170307440142c031000001c0007004181d11400d03440d054002c0826040030080440c1038100a8030200510400c0b9000ca02e00341c114607480829002c00645280410f501d00031240ca6604480011411030003520042d0484580d810040c1e904006090b1207500540340c02d00b06000700307400c081050005100c210011610690008600030849100703079520000141501c0030071000300c000480200b021420010200001c42c8211854102404c409050500d40e10400142950180c08608214400150203000f440000220074000d01071596203038990400d2aa81c031018403c0074081c1c043c000c009000c8800c10310039203043e51103d5a51902c1c1144418400820350400324043da0180100c000c0020f041100c00c1c01005603120607105d003440c17031800d070801a09025241c1e116414210120f800c00c41c15a84202c918001d403503000d540c2a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 19118504 1250 19117254 19117261
    0x70c1a060103090602030a0507080f011802030a0209060715050901091101030c09030210020c0111060c070201210c090806090705060a12060e0406060807060207060219030309020904080d0c03050609040209 89
    0x4030050001d00401500c0b40c0c5c070010500a070b820a070f801891103002c2503180d0071a0ba0329103140c0142c18400901c1030007805114189401c5882503142c000f10303003140c54032502500300304810b00050080e330303ca0074044406030002d1007110031948090052a9001d1400340c0200300d00354050711640388490586100e6410541d032400c00f80211800360014a02940e00030b80f01d00342c0d04c946840065510080e45000b503000c15000c10341003855031000a06941300d5811920080d00300320301c0d40c0c0103584030f40305100748900c03040ca8042070000c03401041c4640c8845003403030350b11840e18078a81791010b410448050499692a04490010301280d115203040f10754280640c5000780c00f011000448a004040d55004501c0c50303010760081c0b006004071600110240d50b1202e0a6510f0560780c2c803000c1c0e80c0d4180510621001d60400310200d0140c03980c000f019490305009080202d0340001c69070000b83c120000300e404036140c1d81d0104007003520000074404e04001600a0408208900303114000031031500c0001e000034401d40100001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 19119754 1250 19118504 19118507
    0x6011202120d0305071202070f030e01050f0c070306060801020306030a080306040216110406051206040b18100609050105010201090317041403030f04031704030c030f091203050304020306070c1a0601 87
    0x8096400700e014080c0e8a8168010380001d010300400c2c0e401c5400241c0c00c0d00c0064001b4002d10803181e9550340222405072854941c3d40035190813000052f1141480000e100e2244e40500000080048060000260103824250b2a24104484090300308038520780c418402c001c0561800182c84070841e070444601d640700d80c0d8100025002c1c0c031541e601d20a0119403141c2d20010095102c004c001c04800481d020b00c030040d102c009102c00c01c8083d60b403091042c2e101e80040342c04158220300710354018103100803150a02e02c81403005480e241d04c0800d02043d10350740d0f10b81004003151a114060260200b4402484018016100180741881c1d640e94a04210a4400440c080005980003c54012501d03001d0742e4403442c21040c4120811b00491741a800705081881181c2041d0a00902c80c0c0704a615445242c0207280548080700c492035a01a950300340a03038680d00bc02d00b401c405404105e0300b071280da03ca0b0303541c0c5010f1050500740f1001409035002e100302c90340c041000403801c4401115152004030286210740d0340c0f600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 19121004 1250 19119754 19119769
    0x405060a0b150a030204030b0105180a020d0204090504050d03060602031303022101050708040b01060503010303050d36051009030509090c04030209100602010b01080702060a0b030309030f010c090801020c06011202 93
    0xc2c090200000080c08222950700342e0082c0003101d002c0c1190a900e170381e07030f00b050040038031492102c24243c5c9405000105483c119901030b12286001c085c005040a44525401003110401c0d0b0302518658440d00500c906203500d8050000904241d10285080c0443c50300c03205003091880c00024440c1d984080c0000342042421894496800401d009108500b080b40703001d801c0d648150b4040d900d4500c40740012038103a000e502103078102c0394556201480d018002e24101c00500070002c103400050b00fa00d000440c1c0d0101a07607000c90285580a0301c0c920180c20b40703452840c01e0800c0005c00318042c2481e4801010940081c1a901a40d0042d54201c019a8a00070701e01c400d481603410080d840380c000c10501189031034070503070982a039107960000c0010840c0c003401500c3c11072003103c041005038441800601c0d20035081d00030096500700a011241000400b400090074030320314042e40844c5a6444400300318040d03010121034001c041c004021450148007144150300d821050040c480221031030300180c4215250880b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 19122254 1250 19121004 19121029
    0x9050d0c0524090d020705010912021c050d020106081605010302030c0d020c0a02010e03031c0b030c1201090201081008030a031802060a03050403030b0f0a0302040e160305060601020607080405060a0b 87
    0x101441d6148405800016a00c020b4032181544d2140c3c00b0f05100b5640001076060540728141c40b600b200602d4011628000d103403440d01241c012001d12040001c4158211041c42c0161081c0083c0090f034441c584001e08403a0541d001000c0c13503019a10040c404c852075001c20342030380c0382881e0142e62a0784040403000c03d807081404040032141b000590402ca400003040d1010014400da036040c0f450740303401d82019900d0081c2c036040c00c503030000e001c480100c288065004082009000d0283c6071200540e40000c1d4070389502484401042e51540c00c26402c40d0f9119640950220340030341c0c15142e032420004170380d6480c02400c003040241666080d482004000f401002104180d000309610381d500054039000300603050a5904901107130920082c80060b207801c40c48400340710300c0685842c580030f1a50b020030002e84510001e0707030064000c50903aa4425030302c00004402a5008000400c0d0505200300020700e001c10042480e010001441c052000003035010541c1a0800300b841d9021403480c01002c0090480421603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 19123504 1250 19122254 19122283
    0xc05190201020417071a0408030912010605060a120608070e070c0302010b06030a020c15010503030a0c08040504060b0406080603060f0a0b030c1f0201050a090305030105010f0306150c021309050d0c05 87
    0x140108550300800940700040d80c03580000034070713440c40302e006031b01c40350043d80030344600ca40092001c00c1c103e06210090a20301400400045a0540d5402c0802c4281d40441464000a906900105080c4005000b090700400d1080018400a807400c46280340c4008003611860801909a041500341403007500544e03c1003200074406130307403410030040040007503100ba1414105400343d2101d14650710b11115a0074101d580180243d85404094041200d002801a41c100c03262502070002083e2030b100c41c42250301030408007850966071810a90003814400009206038441e0380305004100ca001426031086800141d212408a90f0560103070000e410071f03140c42d0070301b5008080a802d80c0c0d801c2c003520b03036140c583c2a4140c00800190312180400c0050f1420b002003d4049103040004000c154844d00b5901d20b903220500e0300003000f545401703070180741748807116440300041d40c7d50075500c003903180c07005015560048842d400c000c211050394034a5110009105c1180c180121a5006c0c02800401e000d07212142000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 19124754 1250 19123504 19123529
    0xd050d0207121706010903081c0f0e010204030218040309050906030a0506040c150206060a03081b0a06020304030806010c0c090b19030506010f08070806010e0406090b10090f0c051902010204 83
    0xb0038001043c0342c0804401c204032240310004a0b0040d40030340e42d20f20039250000c1c4294503200517104048144000100005402d40e9650003c5401c226284180e1b04244420000981d90350716600410607119192402540c809468a0510000a0300a80c0304011100d0980780150155100740c0081d081161040000d42135004034002c00c030070401c40040d088113455562414615030703030b440c030401c80c1d4901080312000e03005030390100240045a0103070058a0850040ca01302401003207071846c2d640c1031092100048810980100c24041050341000001d82d21080c20305e8007410a081503150010f0324100f91040c40c01c0960340f903980700d05540341c0f0401c9000401d1346401040d400740e0349240c6117a072104d091103106492024540b0110b901d000220302d400840c0d00020041c0540e90034954412002100a40304a900c60b940c1e280c2d400c0000c0e0000d203418410b00110102c5541c0516080540c0b0507940316561140ca01b40c0362800c49070303040703811a00fa10138805904507044514000c03060285d0080c4200d4004d00b8400e0407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 19126004 1250 19124754 19124783
    0x50307030b120d18090b010e04091103070f0806071d0103050604021e0d0509011118030c100810050102030f39030309010f06050904020d050114010902040302040b0a06020d050d0207 79
    0x801001c5004001340252030400c0705907650714480101d030018039041d40022500020800c0910b4540c2051040e1030017140c15000f01d019500000349000b8440c6d0245200304400c04040104800920103503030f000780b107400e00f4580540e486918400d2201d000910905060f56039011a8142d1030340d50668010310142c0ca00b401403101405403d00d11500210302c0e0085240c20030000904940041c0038102400080341020342c180010445e061444200f4420003a030148508280c480b0b05507903000709030003060038544075040c4504041c00b41000405047d08024103661003008081c540190220444403248000194440c0d030710b0030303000c0c1d8051564000361442046040e0784400280204044019806002d00c4002000b95854814113030040d0b608604c100366201034590001005401c0203403196007000e1042000207004407404c1000070110400303030401e0511590109092045003880d01c03030024a4142151140012403501d17000039039588660305e010381000f401045491034070016030181c072002517005000101501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 19127254 1250 19126004 19126007
    0xc080f0c070b18040b0d170d0e010f020306011e02030a14040306020a0201050f0a05040507060c022d010f050708030606210112031707020a030302030601020703020307030b18030a050307030b120d 85
    0x100b01c54074812032905c0c404006a24181a00c1141d540c0d0082c0e41b06d01c0b03c0d00c0c1c2c2c4440072607504100500c1c210305444880d2041045028892507020454039400181c076801e00e407000600c0c850b014048010f0000c299600d40c20025000070503a007400c0514030303000b0540b40d0048110072050040c6c1c0c1c0002e1240f400460a11034164041d04100d100c0c511112035075031a503440c0d82850050f90800c3c1c402401c150041041400813902c141c9180070142d001420000085800505440022407410f403201150002800c1580c5950707071008103c1034007442458001d0038813040d900c5000c0d4520014004610800c4001104c1c1c0c1c81c4215001d02c0c102c207440107101d000c7c0660352070303140c0520680f41d14411000034070058540700c0c4c510580c000450003200c02d90f0040403803942e40d0f82d083d0002c0d803006d44001e0540c4074814000006941c2040076001451246010200e82d0030006c2c2c1007001c100300d2041100d40b0f074106102c950341440d441001e50f54032900502d00441c101c400100030614003043c9036110307410703030041081182015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 19128504 1250 19127254 19127287
    0x90303090607021603080a0c08161101030b062a0a050714011409040902060c07090b030f0309011e23030601090603050108070302090604140106080411010c080f0c070b 73
    0x100c200d00180c60540e40c4610080b038540c100307806a00a1a0030b01e40051010400d0705010300780031040303810300341c91f40000e645880300b0039001051516003200c900c110300010410b241c42c0000c44202c0a080510084800c1c0300083c01c50302812440305505c0300c07481c02161070364150f00815082c0095040548812242c1820704945503141c6005000d080042d46084291551146aa00204400b926003490070f00310340404220142070314140980c2d1200052088180d0310384284007a0008080000f000280d015141d070515041650070314200600340c105120058013660407040c1d1640801c4502040c200e0140440c0c01514100c1c1c81420340341c0a04c2030940d548a601c02d9203801140910300988441c452251346d410200c1c19500e0901850202d90000001040141803c0c81c4050308007500600c0454000c50074085014442400d0f442400003420712410b000034808a4103058105600030710340b010142100e500c4680480c4600340c103084a010000661000c1c030002800084050000710f11000c1c0e44110009689a49c1d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 19129754 1250 19128504 19128511
    0xe0403090806060105090901030b090f1603020102011521031704061a030703030e120c06030a020a1403130803070203070c0e09010c03050912160f08071e110f0315090303 74
    0x542c801c00340881e01c40d40c00b9606451524000038000031150f802e50740c405040c0b10000c1e00f00c0c81c0e1885541f15050b19202c0134007059140b4000c2c22411052245940002420355060b00403c034641c90300e150040c05140b0070302c0d01000c04000410700c008801c010500c0c0c1154509102c59012400e4508042400100555070f0030035814100303030186045032031a03184101034446505110007400324031496214403a50400c001c0800303a8840c00710543c0e0405103c0030208000b81d008645444030154001038080c00d16400003682580c0c2c440c00d0074101c1c110b18040c45088419811001c0140c900c250102c005403000d0310810031114000e80c003020050070076036a04000329040320242c2e10f0480d40d50a040d0351604103413007481b0fa03074854032100d0300400318803525410301d1000d60f0000c80907200030f12000e0021000729015151280c0703028401c005071640d4420504100f9070091074441d00344882c1c05070301c410b80041007444816000b403c508807040480e243c42310000900d09020b0049148800c04201c08010343c800020018511 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 19131004 1250 19129754 19129769
    0x40306050103031d01020723030102071401050c12070507080405060c06040b06030c010206010b0706200a02011802010e130204080f01020702030106080a021f0509091810060f0b030a02040e040309 85
    0x5841c3d4003000c564200c007804c655070043e40000020003400f0181c410a042241c20340c0c256040480100002c2426a0311084080c0c8007854101c07030b541d050410074030619074810455440c40741032282005207641e043d480030704030500300300003c40c243c814083c1441c111001480e00130681c81e0f0381d000201c11a5202c01c2e045600752950400100068068200490381c40d40d86801603014044e00d80c203058007100c1c079402800c4140c1e13000340d6500c240c548143d140341715100b0000c40da21210b91145002034000303094070004440400841c4c0b0701e142031001030340c224900e03510449084801100800c950740d45900203004961000c00c0da44980b0704510704d812410740c010b00e40e4038000d800030300403c2c0d02e60100583d00c150860000b5000040d440505801d146c0882590354920250714200d46826100c00c0080c0202400740d4a010240d104041c00c17800c0745404210079600041c142000380030562920701c2c00c0d900180c4a128048480c1c50000015480d03060310b90450303000d010900078080450a0509008005916074001c501 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 19132254 1250 19131004 19131017
    0x3020f010b0603010815040609060903020a11010504031211160b091206010f0b030907050d14060703200705150705040e01090e0303061002010905070e0702010b010302090f0613090204030605010303 86
    0xc100e0038007034102c038161034405d4000d210220b00030340300707902010000b0010b8400075a00d102d50310016100d40650352105020b07034020030030740b481401d0202c419400c2290b1541401010401000060500e070060800601a030500d00d090000d6900c0faa0f05061119500800c1480020004111282c03400e01410030240280e5a0101410100c400c10380e0f00d00003801010070107030b00a5010060701035404000c651110240c41a210f140e9910000b0440090b44c0789400c68581020501c054034010041000303507841009850140f0008102c1075019440d032514480090201800017451410303c0301c2000421f86030b40400c0c1c0451128030300710398000c4c02500a8002c40018038800400040c05900e54043d80d039982031804050f41c91a05d031841001301c4a000520f105c1c00359525101c800000c03a009005040080c0040d01252000c2e01d0210300c028211614044072906051040c410700f00380e511641b4811003141c1060b54403a54070592862041114a4240d000c601038600025000c400c00496401150490340b10361680c6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 19133504 1250 19132254 19132271
    0xf10030617030c0601030f081303060507080610080115020102040b0d060602010c08150103020702120102031806010611060610020c0901080703020315070c121101020a03060f12030c03030203190903020f01 89
    0x229203c0c03194620b0035019034400401400402d20002940314070301d204000380707031074910070310320407800d9a80640c416624643d85070108521950420ba407a9408001196890200d203070b0b40801400480043c0103072540701c0d000079040e51082d8002d40c1198003420f5401c2d92540c50300500f200b0140600054000c000040d4202010a2281c44c0298400b900031041e10111070740407040ea40045009400402d020780e4844427880100711502d10038802103000307071419500d00c10340189104c0d0035850444180c1c007140810403c40706940c880380e00860401d40144080f0707482007000103688801c900c3c00c0c00b0159001da0100192000042c0854001614000c4030720030f0b810785040440007411211191400c0300c41102149044041e50005000400780c3c80e411072032414104840b281003a181c50890300030801110100340d40300d0f018405088000110402003036222584840704e0390701da400412020b00508001c05040c1c010010030203641000042c00c243c10301380c1c83c2c00c01c051180707414000d65440182c03500c1401175203004080c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 19134754 1250 19133504 19133549
    0x1504110303120a020906090907030f0b06090a0b0f040305120d05091207020409060906050a06050906040605010e01050a020109120503040b13080901111002030a050610110601140f100306 81
    0x1e03110312407565512050b0a81d192080c02010703500c68a4181da001c0e808010315055692404480c50150407255400160f564034101c661080320106010188100028005402940d82d10720f0030310700ba600c0341458951140c018102a00044c040c1e500024210300840f84045458105940940712107009020140007540b5217800c0543c0394001c0d00105141c4000c100b1074480581031903081b0f0309100c0e01c1010000b0f020701c0c0b01d0320303040111202500c952a0140e110407080082e450100f42154110301c00b128100034061403c070001c1c1500b564142414107025021403103060240c001c1d0320080b017440c3c00200b80314050442840062081c3e004460488400e00d00c400403d2040c03c403451045d00c0154041241403600d8042030065036406010300d500c80c0c9078803a00c15040c50b80043c0d800614000e481b410300128990501204001c0c65400c01e080130350030882c4140b8075035220070340040c419045801010080e4516480800403541c010044240c80c0d400841c00d0480e52030450341580300e0707812501541070030072141224492 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 19136004 1250 19134754 19134757
    0x1091a0c030f04030503130b070503010602010e160e060315070201020316030902010c03080901020c030c0a02010e03060f1308071208010906050105040e0a020307050423010801060905030303041101111504110303 92
    0x1034a01190351020b00141c0028040c100460304411030208166076034103281e851a5000310100e40000004001100401c1440d809024090141007180058120f40ca0512814544022244280c00c851501040030405076141840b00150301c16200d40244018505104083d01070760090310781828001245440c091494400c0c0314150400e41d0507521800c105905131022030b6840d002410321000c55608002c05020344800700018010040220098048a0740303500014007140540b850081c000d4001900b0420620b901041c02d583c000b03c8126925440c0303c05041189481c0a000d0004103540d4600e44001003040d04118518101d03540b203030341030000544440044802c1d015902c0307110840c0f0b218901050040303420b41c0103143e000ba298a00300c3c0c06c040e42c41101075250400d000b0403c640c8600e5010110040d648812080e0140c12035040c00032816207841701081c0c2d80e1100520180641750449440f10302e41e84904480d100d0001d00104550b131000c0c280118540d18035040d102140c07440c1c114840000541000720 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 19137254 1250 19136004 19136011
    0x70e040905060a09141b040606020705130216020603070c0507090e0c040b040b1504060305090102040b04060806040b04020c01020405090112050705100509040501030606080105130206040504090c0801091a0c03 91
    0x4000e8441030700c4403d01c0901038600100200c0f05003e10640841e8031142c1041041100c0c00c5100640c90a005002c042c0001c4511582001c4110340141c201805a034541c0034036041040c801e00b10050b0380d0301610ba404035281000c0d1340300a500c01000000d01c110150f01031601003003207000310152404c05541c0c4644c6d000b2a11016420852600020510305061034164011540a807001d440400c201c1e481e64001041000c994401d55011540460b081c004541e0600c5a00e50081d48000212300c0c0604207200d000c0b460041c0c2c030a050401052a00080b50f54549da00611320700040900b0543d12903501445940c042d4009000b01c03401010f0440000500d03100d040c80781e4503103507004009806454108414040028032003031050051040410084c2280c0e10780e842200c0c02540900c40000c0d16600341848030b0b0a4030006840b41300c400d901401c078200565035030001c40f030807076408036070001c0c04c0b00c0c0b0381c94080050002a07000f103086500c0c0c182d40078207010501007030300080d482d07550642602d951100c001c2e54032404280d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 19138504 1250 19137254 19137263
    0x3030f1506031404030f1b08040e041e02060d110904110d0e070506092b050a1106031b03070309020402070b040201090b03150120030a0306030302101e0b010309050a0506070e0409 78
    0x51103103541b981d0180310601da40010509030b01e400e006058840803041c0c0d000c4d82c00800b921995408200602408444000800200c0f043c443e10410701600080c45a000d03c0807041d44645e500c2e044449003926601c00c9617058103028100b40400c03110f003006d481c11600580501c1900a050128840c0401c001140c3c820554000901490900c21480280010406980c5505d426a0000984020024034943c02040d01c1c51180004001e044014a03081e01c5051011080760700a032000c0c028002d00d03109030004024074801c244040390b16a80c030584210003401200c00040e410520004180c0240400c03418078900c04c1c0d000381c80e084101c0d80d8600d51207800340700454904481e900410016140340d880ba000c2180803140060088450100603ca1030703045a0043c0310707810100780c0d50344081041540501081c614000403050800901500300103001450b030781254a10500e0f070790781e0812140d40c3c0c02503020940094009080b500e44011900d41195140740a80744280401c0c4940310001092806000d0403880d00d502 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 19139754 1250 19138504 19138517
    0x10807092007061808090a06081905040c0f0b1b0303090316060902180601020c030f070501030b0d0c0b040807090603020a0b03070e03120d180b01050d03030f150603140403 75
    0x1845030905160080b0300200d0b2000d03110006985800c10303800d04960407034010746083c1d995402d10070030014a00300c0d0340e1028062041200c1040350000c1c12460400d042d000c1c0c07070b0b0049901d035224500300e0744002d10790b0448980108418008900300090801a005010900501038920348070109003564a0108881541c0e041e40300f00072000004013003100f1061020f1103600c3c0031032440015400507030410a40040c241142d81500d0030849150fa04004944020505401405039602502003031501c030402c9004030b605042d00c81e01c1c40b8820761644200300003d05c1d0440055944a41c8403040384170103502520601c03a403407095010200303045010740305940c101c0364018102400289010b00503880ca4000800307804c00d00142c5a50541e072074a0034807a00343c0c040d980c00c1729180c2e501c5040500c2e4084070094007608600d40d95007005540000c08610080e070641d402143e2415500382c9a113011406002007060380c8010a041080300344664142031000c00c15124180c505210078158646070820100048030080e000410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 19141004 1250 19139754 19139801
    0x10803071502040504020a0f080a09080f0901050702100509100206010602070608090a050a030e0a090216020f0319030801060807030c02070501200312011e06020a080d0e010e0601080709 81
    0x2a54454541000840c05418071355035000203002c98101e142044c002c2640280d900301517580c050312895001d20200420070002c1c0c11a02c500c4c5082c00b6000086450040000e01c91074aa80298269000c05074000c1004103403210f0100e00501e580c102c00701850060407052400034109002240440c180d50040d40107026540c501241100c0144014102c03881c18020301d00502c0110340305200e03800c0c0c03160181e1900c0c51081c105801b03000c2520711680c01158450f00c140020381407240281e0302031a4164040740c040f400c2da070f00d000000381002085203419201850b00600c400800d034100028904a9400d0740350a8003599841c0001d60071784c1d400b07405440c0183c000701800d200d40d40c004c20002c40c404241c107808410401e003034114140395038050300200d0071303001412004000500c2440100341012080c8090301c10111b29150f4065980c034800c11000b40b030144080f03524aa2121203a008045080d080760090110030180b81d81151614028020300010303018107540420f02c1c02190280307030501e800d08000c2c01c49059 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 19142254 1250 19141004 19141013
    0x50904020307090308030a0c0909060503070b0a02010b130506090c0307300908031609030210051c061401020c040b01201203010816050a0e0408180a06120b040501080307 74
    0x140028a5801030010030f15022000c90304480c040c500c55034440c0400180c4403001040685681042c0c0c3c403001d1294101042070000352008240001121418030403e5220305490b00c2c182e016110001480780c0129040c41040180245a0410781c02101c0903140040c40751101842e42d402807204441500116030711041e1440104850074410482d00540d1044050601d004003c860540f548980251025003003c81800700803031010254000c2687c007400e05607842032841e03000c41c001490300b41e6144280300c0081006400031307011103200c000341c403461041044015199141c0016802c00096900d0041c42008004a25401c05115100881070140c61f0f40304500b00b01e59611039a0030503003202d9015030040304040c0d20480810406903003e048003101510001030f040080c0c600c0964145d0195108010850381040902203030b210258020750441001a5074101c2840c001000f8204114204c0e0815032112000032101e6010100c0c4168505404041c08403098900800065030028004c1910517041005080b0006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 19143504 1250 19142254 19142257
    0xb010503040218040204110a05070201020106080606090115020f01022110080606040903051c05040b0903070305040603020f09090108160b0903030331030c0308010e070c02060f0c06010308120708040305090402 91
    0x178070040001c201401c000d241c026240e0417000143d40400d90202e5038000710368080c0915006410004018000c0345000743c002a003101042c4503184c0191324141c0c02003e4180709100800140d15650029940c0f0002c080b801c203490030040d40c0c80182e8440074400300d002d104010a18000300c03003000000b45107a498020820000309050f034130807801c0c484201b02c041c201d0035160948207441c040ca08030015840c606800c0c54942440c00802411503a00708008840000b80c00000351010b80e05540340068072001d4462140000d41700d01d001080e40110320600000b4100c1001416020201e03102c811200311580d11705030f40c0706a00900448641c103410900016038403818500c4604007081800301607170a15001c05000c00158080710005900240140d5144024076811046890040807034a44c864810701d0001401024030111071402032240da40002c0b0b10011500000580343c681e5a92410f51301340e035a603843e024640794442c48115180a0004000940440c05520000d20964240e1145840e0102110811000303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 19144754 1250 19143504 19143511
    0x912050903010b090901050a0606080408030f060f0d05010b0a09060302060f090a0b0307021506010813030f050c0706030911030a0b0a020c0a15051008010b0109030b09120f0d0b010503040218 83
    0x1d590390300d03c0d800d407554035a9074050080c03544070700001d03460074003101403011350344150030060500091a0500002940180880e03500c14902c40b89904140c44542c00528081d1400c1603d507440b0a1480b103850510806602030b070000c0c54110743c0103240e5030340e454210007174680500c80698040c00610000c00740956003001005407070310003000300038640c4d22178a591100350003d03a406001640314000752910301c415180c00c80c0e00041c090030326400e1490b203106020100b428080c0b00404001c054400701940500840aa600d5404040190340c841c0d519041d00400038581843e003650000c2c0071135030103052400e020990207041d80d001401e02c0c41681d91901c0d01f00c007a50010002c84031a01c076848502c8081210111000c0c1088903a01c40450141010300c5001010341c2141c02c2410b150b4501040410603a030440140d030304580d400070201c1342980d1403071181e50800c0d4050154a8645900040d106032115039680148070186116804000c02d8100360011210750200311002504120089028072203031490640d140d51 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 19146004 1250 19144754 19144759
    0xf03020c010213080a050c0f060313030201110406170a050103030e010c05070e0103060b040e16050d020f0306040b070908011a0411091005090301060e090a03080702150903040603060909120509 84
    0x609a0071801c84a01541c0316032284445410170100c5004000c01031003051000e05044458140900c5400c00080d12440094040a6a4980c0d101c1e54000c040c002e40042440c1c02011500988981e0b881d40090020f824001138103103540b81c00400500800d0340740c446c1340c2c1aa601591490348500b06030005482c11404a24192050700c124113001a40040c0e6070350550286100f040045016a103407001e1005031400300041c9540d581040f40c00041d0141c000c0d101d502102c4040360040c80f01c0d0308a0000c503402000e5504210303014010001000140103003c05a14020200c903510403d46659441c009400c0340d0346404000491061194200385a14054000c26000508451501c0c58405500c0018200c42d0103e16104089540850200a5440c003881040c000f840840c0f1540d18602d01180c01503140c005650004003031181c40404506203520030400c0c0000411501c041206500384010a541e69802a1003010300080c104400498040f8580c0a60310905520984010181c0369001c41a00c0d640c00c6480c0d181d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 19147254 1250 19146004 19146007
    0xb0621100e120c03041401020307030c020f15120906090d0f1404080f060109061a030402060c0316030302030402040f0e150415020d0f0606030606080f07051b030c0f0d0f03020c0102 79
    0x804100c0d402e005041884110004682c0c5a15216010310880190080c1c01c0c1550001c0c8134910209400a210400c29641282e0900070b621080d400214205041d0b4802c11910401041c17401202154015a500a401e0142110320581d240010584d4540d008160000010315804d900c034502c0e80103240030603802c00c4207580d203414580c40701209071820041c4990780d01241d02c9140100b01c102602e05c2548054030802621099181c4011044c00082c44042d00c0203009050000d41e40d440c0803420b2003982c05810341044140f401801c01d0a00902940098900340e01c55031802d0361844c0174440e50f103da2a800c52081d80074180c581802441d403011400020004d54428405401040000d045480180020001c003003000403100c4c04840040d0441d601600f105e024589003503400d000f4243c10215855004507007c500c62800d6850800489903070081103003103490800c00d9a6241e00c051004409014501102000c07a400d443c03241c0c080954035003481c41c42e20089509444000d01d0503200c0c0e0000e05000c6a50303000507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 19148504 1250 19147254 19147273
    0x103080a0804061d01140702030c120904090c08060403030b060a08070c030c02040c0f02010509120405061305031207060f060e2a030405010e07060305100605090102011401030b0621100e 81
    0x1e41c04404c56000c1c03141a551048950039500f2900d00b801d810800c0c5100850800d503054101c20b90f200e0180490102001000c01c0b40107542e550343c0c02080000d940010340c1c928181c3c2e00e20307040d81c1d1100c05403001c60100b4244010220a41811010342c1c5100901e90340780d82042c4c90b0400240c51a010000c0d0580c2000102004e4601680342c03805182d00542080c3c2c2d4164180042090085c21584054840141508001070b44d001c2c100c4480141c0e02640c4040b1102c0d0360f1901c0d8901c42202c0705005521030307030300b501071040603600714455030024051050080000b070201115900010040701c825024003c0ca60070794401280b80b0682400642504240c402141c003440f1017590405100b5420884045802d41c1d1540448222041c051099070f0040416003030601c46410000c1c503414408009004813030070064081000d081a80c402d4020014041485100c140b0319610ba051140c2500b82c1224007030b000c1c0d824042d40e01d001101c3c09206080c0940410041c106545611845001501c0e403110610414403504144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 19149754 1250 19148504 19148531
    0x901050c0604030806031b1513080d0903170901080f0a0906090b10080f06061003060509040f02031207080304020d060204050306070504090b01080601050307080702031306020f01140103080a080406 86
    0xa40101c0c003d403203210091400034101481d04403a21000c01c0500710200d400541916100400c50010103c00c20b041c9d240c031455a05000c105840790b0002c4490b120f409446410315070803d0f044029a0300542104003a02614200309095201e55200700d0300041c803c00000c1d8240489044154110b41c180102080c00b070666200c01041e0b8045103010360300180392400b48444c40c1c14035203000c030040420340007030007030070b00c0c0c280d4081d03140c0c0401002a4028a61044c00c010b0307071b07486540280041c01d8010240e01071801c2900307108141c0d42491008078080d07c52008075900b05c8600340c0c107a030051035024400760714558640d405d1025400002d0021a4125000c1c04003007402e07a4203101440c40b82c1100e944003601c40c0c0c42d01010b9001c0d039072100c0b040c40c107100650301403005030307680170040301e0780701c2998145140b103501c0741d01d000c80c41c5200d40941da8208245005000c61441c0d8081024207907400100000d01040700d03504d5122080d80030a100003448180200000d6184500800c1c40940c4180540800034503201318a00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 19151004 1250 19149754 19149763
    0x7020102090a0e0f1005010219030224040b01080304080c040209150406120f0504020105070204050411030f010c1e090614040504050a0207021003090b220c0305060f01060509010c03050901050c 84
    0x12043c2110740d1a01003154180e06189425071044584c2c40728460140b400001075143c032501d8900f402c0d90140c1100d8034040c1402004212209451030100000b48550020201d40d61041a1421185000f520000040d503c60000940d82a1785820024140031080300c0f00300710003944008011a00288041038061039420b00781d020b00018682511002c8041e41021014003c885c415070b020b40001e4a40014000983d82c0142034485039641906d0008007a125801c00b040385c40c80000040750304d881040c21440c250074040d00710303144680064480c068110506081105400f8500c000d201c0040c03a05502008140d1180c2100c507500d400040301146400d80350740124090300d100311041c1801035000101001103081c040c0c101d0701d8105080c80d04010481c4155124028940007a094211101d40c540c0e404004a4001d41800280d0ba0b01c020312020f6036a403860060348070f910459140d50748060b0318000280c428001c004840f60071005959010200d5865039040c0d0301608048844c80c1042414000c08103841d10800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 19152254 1250 19151004 19151009
    0x1e090e010e040201020d0201020315060705010207151a0d0807081b0601080714030118020f0f1e040b0105040b0d05130602070507090501060318060b010309150c02070e0403120507020102090a 83
    0x3941c5100307180600003e8030302450000c0d85811a0f03c100100801305051081c0c44804c0c540c200c5d0030135640c940e10f06090380a030154640142c41c190300303c080c018001c903865000801540306c501407a50408800070801a4149038000701800655040041d0f00001e03804000410408103207403080c041e280401584146082c0c802d810048056000d00c40500810728a0900345441400450003440449070039030f0014030741c500302c940090044500800b82c0c1c030b141e5903000c140e1207800c0021701042200c10b02a400242c4841c21024094000c501d400c4490303006512800484003500c5201d40c0044c40d1052198103a00107080c010300244600510b000c0403400240b050000b071420900803002415040e0030b0040403002c80b032042e4010014075250904419104200c020b110050580042d40000c1c03443c1e004005a01900d62032500230711005841c0b0b664044002141d000c081042c2c1664201e4a605440d2420320220b2603041d00d002c0c0c089082105404031715906a000f4070b6002201d0310015081c01c10403400314032519202d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 19153504 1250 19152254 19152269
    0x30f25050405042009041d100207020906030609060708101805040b01051c02091005040e06010914130b060d06050c090906060f0712090b0703030207050d030506011e090e01 75
    0xc04000320715044c003406104000302c140440b1804640f44040c0d07210b2141040705400399480e5244988900300d50000b851325402810245d441d541c000c01800350096100b050221b00c92000395020034128200007503800d101c0c600440041503d511903200655400100038005032000500203000314882188020301c2e8114055450003141c142000c2c2340814103100140c000c14000d1110084010f920518a070714045c8050f0182c070110f045444055001080c1c0003a50007560b08142001c0c1e8100107a60001801812a214003074204101d5074001702d8045044030030780d11288070201802d42000840c1d4854440b9070080c00043c04a0a22041d07982c9d0281a104101d035541c2554601150881460500a414941c8500201e4007a80b621817017281c0010140070313142020707080450913000880514014440c503005407000c49042034950410340740c0280a540070800031205400303410241d1050318002d0040e140901c1050b1140400061108444400101000003502c02c1040400c4001510692128000c0c080c0420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 19154754 1250 19153504 19153507
    0xa02060a0c1103010515061305090103110307150c06020f0c0d02010b03011104081209010210090803010501030f0218040209010c02040e06060a0806010b030a090f1a0f060303040302010203030f2505 86
    0x25410710004a22080720600c0c0070f40d060504100746d040800c0322540717629004480507034442c0c42e0240d600e0708085850f00201c0c0c10400b4180044180040e016060b840114220100c0308c07034a03160503040c150916442d03400000308100d18841c1000600a4014003005030421407106d00304400085c0e09840c2000300c611403030142c3d40d00c03c11200e02e400d00b80201044039203003100310b5240501d42008103564011001900100110109900880b40e00c2800655051640c4140c140301a8125041c2139170150700a02c1042c0c0424076083c24851801124020b81d803403240030f001e0081c0254286000d22010394000c11800d410408100d42e22030042e0348500c0741e00007400341c00b4000d04c4240b0303065091040d11901600314640980c00075004000f0b000c4501c040303960100c00d050b0003080700c0c501d034030740a01c0c164081803008112103007003504030b010407403181c128502c19010440022001d8a8400c1810b450b0720445c08041d0050b0020400694002404841c030b64000c03403070b4840d00c07082d41e0546004002c404845400c05002580 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 19156004 1250 19154754 19154777
    0x70510060f06050403030e060304140307030503010807060e13050a06091404120507050304030609020123030702010b010906090302190503030c060f060910030b070201090803070507031119030507050a02060a 90
    0x340c4801c210054003036810a20301e02411914050403a0040c1c3d49103070b04c18400040000d040040320f08024250003030f0082181d80356500380c0f5002d01a0341003400b80145500c2040e20008100c0d100d0807038071010344000b50042c2103141c901060000548002003a0101407074680c1d80009240b003480c070501d640b02d1000d005c030132140d0600b46410600b80c06408210010084103208860200e031002c001c41d000c80c0c1d0f220000103088006480180e66060134110001c0002ca103030031388540d0b91127545004610071308540c1d00030801c82040e10015031304421a4090f4030009240e1040a00040c1000001d0b1940388140d0104032044541d12070000c0d2840c2c1c050b500141d040d4200d84140704011071441c40454110f80203c03502c002616103212004903030401848081c180b800b8a50201d2400c0c7d00079481420803d070807003071040e540d1a00c4800039040313500803d000c80c0000c64402c0190800d030340c0420074001c1003480d6251141a2061500c1c111019000315a094038280106000000141e4840c801000c410260740c480104036103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 19157254 1250 19156004 19156019
    0xc09130308060d030801180612030c06050619090b03010204031202150703090515130b0103051b090411010e0102070f080c04050109020309150a06030203070e061002070b030103021507051006 83
    0x840182c50740b030040711001000f00c0001d130044201c0d0b05403410181c500d20780c181d12145150240c00309912180300c0041c0c25440b8800d169000610300744c49409484140842d468a00902160000d04002c000740303089800003c0c0100320303243e0043d02c1048401000981466141e07100c501d031001c2141141b00c0541e00c800050340c0c002da13203c02d07507550101090800308402c8286403503540d202e1901111419840c01c1140c0000e104002080f491443c560700a6003143d4150b84910303050755101c0a440110194100d03202d81c07000146041c013055441158041c0c145000704070004019101c0c03c814264003410350041c003a010851034450901d0f07400808100d0300a0074a142e8a806210441e501a00070861581c01041084010000010146490b801c040181c582550340d0080a0f0000c01350342e00001c0d414002d03d0310016020944200450007448101d41c41d088950341c400060745e03501400e00c103003020084244010005440d04a08401f00441031407031072850b00c034060f81e5441c10303c2c10b01c2d2031055503103948440612111 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 19158504 1250 19157254 19157267
    0x2331206010503160309020604030b04050a02040e0c010c060c0e030318040b0a050f0f04150602010207060506010206060907050d1e09051002040b0d020f07050d02030d050601020109030806040903020c091303 90
    0x204082c24a00c0c40c1d800d0000e100010b8a0060380d40700c1c1450b8407044288210344440301110000c0d03070000d4185050f0b00309445e0841d260440d03100c040e40310703c1c00e0101a0f100c40902060034070340c180c8140c650081011842c0c0e5141d010302071003101e500500c150500007560300c0c0c17001d000034040788042005003040d140c6480104400c0720340850415004002c0300f801842541c5850b5400204003004075402c41ca002d0103080050050308414a21920082e001d07180052400d8054000c1c011640c441d020510440d80e55000481e60746c001211801d50016228010900060259004180d548070b518804201050600c0c0000b0201011890b005500303540c5640d1101840382c140080e0783c07d101f0b401800d614245c5403040c0420240101d00740e90000784d6000601c0040c40c8400e204850115611105a8495401900000e5102c0d005270509044440c10040001d401c1d600c184034103d00305905850303561064449a0601000700080001202075200b169918519a5034413513078a4480e0101c6038900070301c2ca00500c0d004145 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 19159754 1250 19158504 19158511
    0x302030118030f020c0603041b090e07090f0504050601060521130209070305010e0c160203010615080a0903121a09010f0602070e06030a1e0b040f02120604050a023312 73
    0x464001c103605c02816500e100c01c0f650001d80242c0c08000c40130b183c422204031130043d907005003842803616504003900c00c070105030703c4211001d0b040308000c440007014040f02590b004071001007050f000f0b0f07401407010f40d0140020380310818100c408124050b4032007014240401041d84e041b00e04114044d8440b0451418800c2c2591084003032409114652418518905503c07014091001065022951803c3e00f40e06030107414000f0f40040090201554130075941d48514441c2c8032120019071440c0005042503240d00a0507841641039540181441001244000501ca020803000344203506065492103640d850b91242c0c064104013043c0f0101c40d15001010b0b09d000d046a219802d183c91540402c40319650104030704d484a0382040b02c1a603441c002c45400c1d0ba0b2070b44010b030010210300c1d4800c24001480014040c0c018824070a0b0b0b010000700c9010400140d48000c2120000e00d59441080d03000010306004580201d0808003210b1019a500f040850206800070398030120550301010130750120184200030803070740 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 19161004 1250 19159754 19159757
    0x3020405011d04020405070203070605010f06030c020d0c02060304080702040c0e0102010f14060906120d030605130506030a060f060f080606031006030302030d0504170703030e0d02060606090d05070302030118030f 93
    0x40341c0300740b10161800ca280040c4060321aa546030006200345000703000300e0b000940d01100030040b643e126501040400e800c1d0051100003480c081002c600d0b1800010b4848250704d568980d241c2030301c019401c101d41c82d84002c00071241408280060070058503a07002c0c090080712035444222480111200090031120708c400c1c400c5055042c41c0d440b401c48840c1100aa400c000c1c03d80301501c0300e544d00404141e580007900d18485140c81034075040201c190307141d0b100800380e61044071031103061000100340b0002c1c1c403000d5403020343c150000c900450000d02203900600b0054101080414000c1d070700c1ca0801c600007150360250348150041c00400c14545010b0180e0309640060007401c00041e030075501c00035524010003a8800659607a6400b24081c000c0d07109602c1c440c140711640640e039808a40c500100902001c00081110b032003850141c482c214004202c40c0d02c154809010a811b0095403820005402c0500d001610140036040020016803020302850001c00c1409907400100b01781c514000700384a10b0b0090341d40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 19162254 1250 19161004 19161029
    0xa03290c0405060a05070f02062a03040605030c130807080c090a0c05040303050f090432090c0d150609060e0c030106020d08061c030305011403030418020c03040b130302040501 77
    0x41265030383d505407140c0319024a04161180c0080ca00b5038031000c000c0c6c4019601801c0171034054214103d841007d0702c0000d51002c074500c80120101815520301660090300c01245090000031481124003000d888898400300b8420303441c0d9911410b0b2805c0600640000d0025045041b02e0501c41c04c00804044e00400401c00c1004080030070f45000b042806503000060030005c002075002101c03c1d06100350349410800400400c0184901c0c5d04518904041d28600450003040380e107200c01181002d050f05108081803000b40a030800c188040080c004450b040403266000c0d4441d1402d11802c403072080201030044100300198540c2840700b41108a0b0009258000001c001c0005120903036010946544409040c100350166845a0000601c1072a00c0240305c0c0300c05250851040038140c5c1a007260307040322014142c45c659001c071803003810340748d00c2030b80a1040e60303a02d0b00c481d03042811b2240c1d00420754060307240306503410301c1d80703c0e941001e00d6444204548505030300306c24240154649841841d00400300b020401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 19163504 1250 19162254 19162259
    0x10e191514030103020105070c0e070818010c020c150d060803030702150103030f08221209050a08060c0a02031210060912030c1205040504020a05030907050d050601090b0a03290c04 79
    0x80071103210500009042000200303202041100701200c0c0e80140264625083c46e5150800000300881e504480c00c0001d1904401d45080f40541032003001594285540540200d0380b14a00b44070180c1e0b402d40400e4204401000b038842c50300c41038841c20000c0d11202c0090b582c0d80c148420300910b0807d0b010a040c952035080c0c0010000250082c0340d0021484031800c1c0404207990b0b1114100a9001c1300c2085841d142e02c030101c0008000242d1100c50203500c180e11a10801c1c3d0b00d400900c9184c000d14000e017003640e440f03032001c10002111080a0540c01501c0d1040b2480c14618880d6080b221030300352046400020784080510106c2e4014000501900300080c020500461544008014400410000e000c905403641d01141c080c3c82075040b0b030007a100142c010740d59800424002001d603030089900e07698500076580701154034035112070304503480e58014004040c5a401c14030544010409080e0584e40b0011481e00000052890020030780a43c031941029958820f4041400102c403034001c250303c5002c401000705 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 19164754 1250 19163504 19163537
    0x30d090513110d0b030102070c060e0405010806100608060f0d031e03050606041e050604060917010603020630010e070e0907021902060d0603060e0715020303060906010e1915 76
    0x240c43c010b02514402103002c0c0d603010301080c0244641300c40544116041000400e030a50065161348400600b6a010884c0f40e0382c0780c0d240c6072107480c180e030740400d40c19a000341080a00d204038651904001c2c0104000c200c0034000001502211848800700d01096400d40304503110702050180c0d107503030403084c1010b000e1440d080000411500c150301840707150300d48107408071032590340c85c0c1c1c100d001030200684456691a110840941903446e113104e1007100100d2900c02c0d041020042c01004101d07540a42401c2c28550190351451005114032a40790b031810140e02040304041032034498900928290305103220504042d54000d1580712540d0b4910b0040620350188920f10713600242433940c07010b0b00806042c4040c403620024419101360a42610003074200710300030051103411307440410550202c10466044507034400182d40c08010509090f00541c0081c13000035030a051803921294401414900111400405800a43c07041c0d0103040d030300709181c0d0b400c0e014001d4041c100c40c01c407031408040c1020b16910750710414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 19166004 1250 19164754 19164757
    0x907170106080619021b06090c01090f0302090603030f030a092a030305030901110c07080105070804030504050d02010e090a09060c050f0d0f020417010e07060503040b040b0411030d09051311 83
    0x429880030740c8030702c5100803100341e85c1a146007040c41c040000120b4900c0a425940760b206803002c481600400441200c2d40d8040c44100084902d28200750028910310303000c10400c1351004103e03e030540810400704a032103204000951244840c980e000403504054100310911000300800c02c4200c500499013440c40c020301c1600101100d505260941c0e695882c2d0355014054403403644c01d0342d8403032400315070031103403010100704501030714100c2008021503aa40030040743c03d44000d582c090003041040006001e030342000c642d200007907801810203140b170092080200c0c000b4070b0210f0b14120b4581d510000700e010440140909001ca06603407501d1410111160b000120303d10441141e08075443d44c91440958185c113640540d40101702140c0d041c1d0305036180a0307400f0f000c3c0c4189040c0c0e1640340a0341d803000c1200c501500c1a240501d4001010b040c1d40c0e5a595106001076074064400d075100d500e400c2480782c4a40d000c01a1a00702c400990b100d03c803c03407412050206005121480c1400c0ba81024454041844c1e03c80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 19167254 1250 19166004 19166011
    0x10602030d0c02070801110301050310020a08070e030c0604060c060e060105060f03060a05100c0c08030a12021309050c070203010e010c081b0904050a0605010809070f0605070606080609071701060806 87
    0x7400080106000340140c2c9400c8003580f0298944d42402e0b041c661049004010398108c6009805440c1a041c00d006100124441c09041130040b4080700003245200380714510030503d18a01074211051003a10000044c03690308141d02c058000b500d02908001082850f008844490703903a00001c3c0000e504100010f88103000c2c00031081090324022000807002d41d240380ca041300030f001c09410324001c5122010b0081c03903200821000d451445407505d0001d40e00900200302c41600a0b141d4071406005062400c00c000f07540a00185c01c9021540c0c04d01085032001c502c20f05000f065100a05583e81c0228414582940c0c480d400e07034801a45420690310130280c00c0445103038098500766a00c051078418911585c2140a03074210f064120346030070200030403280c4c0c983c0a80705440c001d88030f55400e507540c00f04203076494045000d0814007403921402000f40b18095005400594070134180401c00e01e496243c0107242038011620070090b0b82c400b41080140400c89403170111055111341c02403100d40d0400078002d03520360016 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 19168504 1250 19167254 19167277
    0x100612121106180a020909010b09010f030804050108090c03011a100503240310050907090e0f0a0803060a0b070501050604060b0f0a05031e04060504051c0e04020a03061208070c050901060203 83
    0x422502c00b01030024804155045c2c0d0060124200341070404421b070080c002004200c2c01600e100300081030041080c525202200d922804851074503007000011500240098801d030144d20400d040c13040580c3e03081c052101041410b8510000e00c45580c2e0400000840c2800e85005009042003807047c0c84011701c250202e02428a94580c20440007000460320380a003900d01c800340315140206200090b000494020103d8818441c1404048005042503442d0549024101e10b01c1d4458a111400100b040018690082009020509440c0e480c0b0014686901c40303c0102c5650350341d01d0030015240380901c200c8002e00300ca02c00c1c890600b405c1a4031900c0c00d100e51600c213014410048001000c224103484c2e5182c1c40301c0406e001e601b46041c0b9240a40c0030b00029641143c1900601d000c4011008451030101c034041501c0ea90402d003d410324052100951004508004142d2944004108201c62107040e002451281c0308481e91140181800008050190400b620440001004114180e07002083d09d5840006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 19169754 1250 19168504 19168531
    0x9010311073509090a09050a0203100e060c090f012d090312020304050a030b06060f07080702090a020910031a03070611060108010902101b0203010c0f020606030106030f0308040302100612121106 85
    0x25400d00c20f19000c21a00c00a5140c810550320400812480d04071420cc0e0a00c1002c80d0900e071941e01060720369000d401a00c03a08014880f503d1030003907209400c0360b05603114075140d10303c050301400c921502e1280c0710100721000c6005108200100b01144c0364060f802c3d03c0b644055410700f410107002640f0841c0510000e8a21601200412041da581c002214550034a83c09541d55821680c50070b003405811810007079200c0c2d0340910014400007124002c80d021b440000380348a010048841742a0010030300f0180090030030000503102c5500c5d845c10840640641900d80b1580100884030030070303928144050b0051280c990400e00d00c800140c03107003000c284c801c2c11142080306841c40c0300c0520844906010502030340c1903003002e220072100d64004080c408032080c0e0b6401e03241542c0e41c01003458280d0b0076900c00100b10314101c00c140300203c2d21640c2c4454116205c1c0c13041e90a4403010344280c42c107a661a0700400144c02c6c1502c0b05008121070711080c941e010441d81000704035100b050700c3e01510350000a1524412110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 19171004 1250 19169754 19169771
    0x7080a1e051203240108070816090902030403050417070b0301031202010b0307090209040b0405040203070b0304020d06050f06130e0607050c0f070e0105011404030809010311073509090a 81
    0x28080700c0414482101841e46a00d0101248444440c80780182c40d0b014181c600e41c02c070517500c00c04a252060407a900c075031f201a2a240042d0103c1d03100304900c0410000244030203e074045050000b1801039000b5911140c03540d044c00c004c14184295120146426480700c08100039200813102583c0c116034025020b001d941e040b428081c0c1c00340003122100c5ea8180a495004200d40f100d590151841d41030584007023140780001740c181b1080720001e4501a40c10b9020603410020154414000d46c1e0040c4003400100e0f4010559071880c090390020340e111a00444a4000c200c6103041c44101c0c8e001d9040e0b1524140100c44151400c1030b264071001d0f01e040d041210020f10707580d4181d000c10141c030b48009400111280302d90741d00107150822000b0301686c6e001032107625541420746181c000352402d0f00d4201c4680e038540600c002c015801810b003804118000740d400c0c0016404600c40c41140c00c100791248003400400220b10003401e04400d014040030000500c1800b4900103a104d00d1301d1031313030301c080034800c0000c4094 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 19172254 1250 19171004 19171013
    0x80c1306080a050d030b0a140405070e0904050d03050c0702011707050405060d0204080d03061505130e04030c06150f0324020307020307030f03060501051c0e010c02010e07080a1e 78
    0x40c00307401848480c820b4000701020010001620313011008955001c0100044520402c03105140300d20800c00050030940d403803001840e143e4000c98100c83c09003842d800c2c03040041d02144507040129030554194014002c510744c080e07018020300e40c1c000d0030342040600d0031500707900180c0043c962600c14101c080e2a0b0b00003d0415006034200d901030302c002003070301e80c40d01c00d0107030101e010358004e00a034000d6002d1011502040790107805444143c2c1c1050320a103a03e042c0c0035400b110503400583c94001d10300340752927000514420980140e40181e0182c0da81341640c01245c10075805550400302041403003031031114200140b00501401200b0349500560410000e10400c070301b448110300c500d06441321203100000303004030650008024450782c2c0c031903229204100c00d60802942294020f21440d07020450400011100090655240b040000400c0300001c40d418070860340740c2140c0c3d000402301d0160303648980405090108001440c02405428000d014440c0c45030755100c0d88540c4040440302d5034090345422030422 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 19173504 1250 19172254 19172261
    0x90d02030105090a1103030c030304260a03020301030b1003080306040c17090a020108010801020f090112020c010e0102180a0803120606041d010321020d0e040605030106090614010504080c13 83
    0x4640040c02801a828034500d02c0e82c90340460801201c8108111619071801e080c04410345080f00410700c00f0398216942c1e034880c607040500700c030840140914840060b03103c1280400280c104440e2030754005841f581940b404400388040a8040421212039010030000561203400704d0b503100c4015a000308a803081c4c280166540340c000703041035a51001040c04c00110140010700d0404840c001d0f80c400e010741c1d81c0c50400900700d03c901c00c43e4204a42041010b510301d9401203103000d040c50b2150100501d000442c80c00c0a003103540c2c1480b0240307141d400080f88003100a07108081c030a00d12041743e40034041490100000e90302d201d44240c0c522010818070001d1480e969613003c3e5401000480000c2101c0d404e40c100d400740f181401d0008660310310203107181c1100b41071b4060042c01e50052540040c00460001c100c255554044001c0f5554856102e0001090984003801204000d005101011030720600388041c3d0141041191003541c100182400f0400c20000c000441240120090b641804880103e400c484041d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 19174754 1250 19173504 19173529
    0x30207170a180305032d04050f15120603060604020f0d0f090b010b0309010f02030103120c02030708010e1c020109030212090a03020406060810060305010b09091906030f14030301050105070809 84
    0x8030803002c4000018004080020301c56402d202004403464020400b00a000300400600c0d143c2080e8203000034452420310221030460280e0041c90b200c11240005000d24140d0b0251801701000d45490702403044508082000c1e98112804880030360524083d40d25605241c012100007483c500d8a41c0ba07400c14411556000c288040d03005540359001d0341c0c4582c2c1c02c004e250b00a07903040880c1d40c68840d445031005810701c2500d06884d4408041201079492000407203100d031400400760303410300030200001400042445107550742e83d03d02d0041c02c540d48104001d030340c0c05401e0380149829641400340560003e9070205a40650100c4240701c1c0d501c880c0440e010030900000ca0700001e410910302000400c41680021081c0d10070458081060f480c26190841202540c8082c0315135078102c1c4051005034402d10b0310b80c0106611a411000f000c40400c0072400420a50ba0981e00c1510703520207030748554041c0070b03542e100b0388800f03c000302c011451540740100084c514400c00300080c180302404101c07061142d6034510429034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 19176004 1250 19174754 19174787
    0x604020f040f030c05010504180903030f1b090b131502150a050f1608060105070f0c06081608011a0c030c120c010c0908100b0307150f030c030207170a 66
    0x1141c40d01c0d211400c0304503507140026100300526a20008056100390100c0702034500400804102d2841c8141c104041c1011183c218103041e2642d004050102d16442800300d082c588042843d215400894040c05d420150340011b0000c2804101d003060759440024540102c1354490b1803c002d66614203c100d08200510340c200e443c000d1810203000284800e5004107004000d071000800239038842051458090480441003408a1000b2002400a600401c081d0400d1805120b841c0d2240720181d45422160707021b500134001160782d41c414024032078590313441d048640c0750605043c6220b5050020142c03404d924140c003452030710800940d1500d075840500c1512410341d00304040f224400c1030583c0c0c0c06580c2c0c001c8108441198a01481010503520405081e0200e500c000d000d000202c0003003010310050300105140c0358240c80b81c041c001131004180941544c1c1d090140d40d031402c07100782c01e180c0101950003450800c810140103014510104440c0c1403400414002d248600d075980b4449402034440c80c4c41500c45c0b20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 19177254 1250 19176004 19176007
    0x50d0207050303010f09020702090624031e06060c06040816080d061e05010c150902061207020c0405090d0c03021006030606090b01140f0a02030912010b01031d0a03080604020f 77
    0x300700300c000070155059a960128107a0029228a4803c04a00481d2000795120810802003980342c100092a44a2104605010310000c481c920703107107503141c1c030503515030454031008030a00034140d0007000d0705074112508039919031a1120000080c0c3da02c400281014000050009207140ca06000e02d90706e00f02c0329030002c071003a1280561024000140b1b0a4483d9074041d01c1d5881c0d074860116140f00f18402655416100c0e42606450703620391036526000410181c0122755204201070140c2e5030240548071070280350f06c0c0d01c6581c1c0b0f040c220090402c244001c45a01170303030a2030217010b84043c001c50007800385e111a2400c001c5018031410100e1031f2500ba11540b280061501740c0100c188607040e000f110030303200d460105201030b4100600458100400080c1000c1180003881190700c3c02946400070940034407070748101d0303043c030014000140441c0c0c496141c1e15010780d900c03642d4403690358240c000c1c41e640305080085c2c0710341c080c7e04840041d15072640d1a0020104422031001440701d50b00d0342e0598a80b00002e02903035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 19178504 1250 19177254 19177267
    0x120f091b0613060216080f030d051b030907030311011401050402070204090b09070503070b0c07120c26100603110d0609050303070201050702060906010b18130f0b0a09090c0e07050d02 80
    0x1a4484a0105c014141c080d00301001290f0f568000640400512110004500c0d102d0100031403002000090800842c4040b000c40f8514118082400fa6001d88900c80103064100e2452030f020f020ba05845003103001c1641840b84000c02d40003800c03441811640296005079503a081840024001c001d1280c0040c5210400c10506c800300c000060000f0a6030800ea044681042d20b441e4000302500a4002c44601076105200c148040d0b4180512100d000d4031690000729200d44860810446544050070300013001c607040612110380900f00720100c501c481c0d0080402449045840744060840b034554401e000e03200a41e84202000210f5021280c2d090708102a26202d04002100a01800c400e80d00b260062040c0c030b001c0f506015000c03441904842010080074034042003015030748644a40300e00d0259012085540d400078a810b81e0084020f03484d00c0d2540010440c900a041003101c0c10641c20808030949484889000984840308880a541d02c2081603121540c982c1c100321218071401203011031043c00070891 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 19179754 1250 19178504 19178507
    0xd020d140f0601110c0307050d03020f0102030a0b1c1106090303040801140a14070206061003020906070309060306080d12090602040510030203060108011d040321060308120f091b061306 81
    0x240c42c0520401da071108040d880380c12001c1e80d62814103050a0303064010280400243c41d0001d0080d02c005c0c4a030054444480000001b5422038008683c5090380c03540711901850a03140071002c0e004054042000c448600e01540c07190a810448a1401070103003900050181d0156810401e4600a205543c001d100b00c3e000b40411000b520015200b14034031030f042c12110789401c0d2242041c1ca12543c151307401400d540d91500d040040301e102c81041c84040c980e00b040115044c0e00c4034002030200c14003d8031075144030b91038a2030007812214a80d015031015042845240c01c0240c2c132034081c0f910081800f1003c00c0811160601c90008e200e560701c100d6106075000381d030f008841c0d05038004d14414802603da450f81d9a98070400910b0b103100003115000010800340c00100040d0061140b503011101541004010020b107005410468a054005590300c07800418203a442e0202004400d13406070041e00c0256150030301541e102d580703d180c0180e400800c190211115004d4840d030702075403181c100c2290201810ba598440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 19181004 1250 19179754 19179781
    0x51017100f11040902040504180203060c180a0605030601020d08070f0c020307050a030b01030b06010207030f08070f0804090e01200712020111030a0b0906010e0a050d02010905030a050106080708070602030d020d14 93
    0xc07d07000703074203100b05020107803040c01e07200160075006400351215948070410002035502c9600010144170443d15034003105d44440c201c580c080c04031500c03041d989040150001e07103801080038807103041207681000c1180c0f0680c02000c0c02024140d50801e0100054070784000303410880c444d00301e5504600c0d000c0c000404d03c80351010150407240140302481458542c40300490b16400c1c540000340500b0085140d01c00058081c4000700940c60003005101d0340ca02d2950344490f142c0e13000343c1c054001240c43e0319072549019802e1281c51915281c031910414080001003941c0b8070b40c0207005000e00b2111030030782e09100c414000c1d0085580154074682c681d542e443c1091503040103010000700360303024a21450008000b540505540360f9000d10040c80d207504c2a203040304106006804820490400c05240e00020b440d44041001039082c07071040001040c0d0720f007040f8201e40351000075840038440e603000c803c04206540d004030031505010f403074000150345d807000d2003110000f9001510350510041090420009031030807003034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 19182254 1250 19181004 19181009
    0x7020607051204031b0303050421020405040506060a05010314060405070203040807060c0b090c09011401020f0a0b010509061c0303150510021c1404050d0311030301030303051017100f1104090204 85
    0x110240c0d444210b0340410760517103086010050124104004c1070056044d490040790308003030015000c000c4a00b03158040f82c02c0d164203481c102c417203920010501100c1e141c89880003000d410280780070004c83c40007800012039480042c124078041d40d0341c0e10204403818400c0c0700301c60282c5494412140440d42d1940000c04d46018a01c05982e40821840407841101e400700e2801d00c030400003441c0d2007060342024043c0307007007000525445066100d02e03410380500e56030500040051070b000d43e0b07140b219585440b003407021001d002445a031007015610b0ba01580c01d420303840400792064162030300090070060000d11102c441496080703207900c850500c1e114990954001041c860042c6010300c2d281342c54031a07040a40c2d90301400c00c0070540c8081e0900081c086414031607407100040e80070703252110940c1c01c1c00034001c4c10341c2c0c402e0704103a0020751290200031100c4070480c403820080011460608503118541100d81e101e0f10340009041d04191110f8618401a403640c011604449000855641d25a41d0b0025640258800d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 19183504 1250 19182254 19182263
    0xd0f06060f05030a121e0c0605090303040b0a0902010207030c17010b0a06020c04020f120c0408060f0708040308090c03031305010e041104030f031b03030603020111060702070b0702060705120403 85
    0x9403001c80c1d100d00340003408003160b80160051070030f0006550b944054001c845103080410000b40c0c0031403501c00302d0082810800c20b268a40400c84110707403d140003600d01c02420282140d10070024000020342c02030300150f000e2590540042c0315103a07840102d0170b21001d1307403000d4600301c40e02c1004034205290100c0007062180480c02003211612100a02c414403025106a401580002d50006020700700340e0001d10314060540d801501d0121185205d0f01030313841c15640303012030f5100814148845501000240d8100e5450b41494a541c60715801c000c0400c81d00410003010002400045039040104220705c9150140090941c0e455000310f403541800458079101d0240040c102c9403070b41c09207092920842914640e110380c01441e043c1542c0301d681c40b0707001e005411800c00c01c0a080d00001e003800c1d4a41160254440c0d900815014554000104001749041c0d00358916000b420a011200d074000950104403030a140350b15417508440d0002a51038050700070058494001e074041660721a0030b0b030b0014030a880c8903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 19184754 1250 19183504 19183511
    0x30702010f05040305160c0906081e010204031e03030f0c020c0307050a0302130c050403060f050103030314061e0f0406080706081b0a080a0b040c0201060611010b060304060c020a020d0f06 82
    0x81c00041010340320161000340101c0c00070065030318843c10300c0da07290035100d000c0c08040004503030301d01c0302d0021039407140c1c000003854100d440080c00c0c00b80e80c0d002500010000000035070a16007552144100d00b04a05603500c2d1290031381e0400d608140c025089482140805503042000107000d0390701039182c0341c854058920a0203580c034042550300e003c01d400016290083d02501040c0b8201e4280d600501c07a41500c0e0b024131006100000001d2924095407070b03242c042c0c0d6004903147d4910b00d00a016107015048007241c468202040000c1616030304141090b0030110040b82070103405980c00700c6d26000c004072a044e00242481c0300440c2c4840c0014aa43c1240c14a98516041c0d6441102203d2030001607070781d44003c05000c0241401d080d101e61281c540000c2000b02c00900c1101010000e4110ac4541c044100940d44a102c100102c94001d0304401607402000d00034000c159004002072aa8030000700300030700c0c8580d80c01c0c251000720f10801410504590283c00456000b841d801c1000000a902d481200d01506 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 19186004 1250 19184754 19184771
    0x18060302031b0f01021f090c03050a031706100c020409020a090207080304050601120c090509031c0b030c15070b0a0f090503180a03030801030f1a0a0608120f04050108041a070503070201 81
    0x100044116122510f40751034149000c0c0044800e01500e0347c180e054841e02c40b0342d840800480c0003441035035042803003030301c80c98144d0458500404918400403d244c2c414031203151035900e00ca400204552203182d04490016030031220344002080108a500503485085c8049064810081c00301d0007140254040c000329145680d0300d00c61131021002091006000050708401040081d00c0c9411090b0020781361419282000b141448000d101d0001ca815982c015444895548040c2400d20020b03995100071f80f0340c001c2c4641c08070365001d8a0b10070044010031a65a0000141001c40c40b03a0012007120b8091005000c000303007a080aa980380c010500d141c007820410b0301450b64514100700d500d42182c0e81038880100e260b1840e01c4000c0070740c210490076601010302111300288070030400c241603c2103035280000100030b401e0501582ca400c0b0344a200101c3c2013010001d064000400701c081d601210800d10344510290745500c1c12600c4000e10b082480349088001041c0094540c001c0081d500c01c01c0c06034020058187c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 19187254 1250 19186004 19186007
    0x105090d02010e060615160602180103140603061b09030a0309030302120702090a05060315040c0f0b03010b160201052701031103070804020402030703140f09070b031018060302031b0f01 81
    0x240291740c400c2e808284202c01501900001019000c0d0250b00c60007400495100d80707552003070b607010030900c2110b9009040c981d54036603014480c1c140182000401d100d080d00d800000301c0d07510038010f04031000401451000600a901d018101d903400d540250503151100114680a4185012800700320094060604008854000501561251070700284181c0c3c00b80c40300e50a5100400340500515014068125181c0d240d02c0c00d9a0300e64001c9100320180d0306001d103400300505100103590001015000204010082114458255400969600000c00301301c41715100599071840350140d0b81c0501c80040510004059007604140025402a281031100d40118000c2c49020702c030890340c80c008500040040340c05400c2c070750b010315401031890400080d5640603144000000c242264542281074140e000c1181601040c8031180c000d24108001d54298103245059824000741d90103001c00c40004a240e040801000f0b801c01c100840d005800d541c071140c105041000c5654207890010b0062520914140195 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 19188504 1250 19187254 19187263
    0x601060f140a030902060c1605030307020f09060a05030d0305010603110a080f07030609060b04080c01020303040203060403050715060806070f0f0909020c070302030303090d0806010305010303050d05070207080105090d02010e 98
    0x100c0e00d6680c455412681184001c00341d000401000d00f0140d5406207040180c441030020003510503c000204000111040d04d0110380c4810b0300228005c0d0002c1c42100c0042e01d4040001c082c2800443c0c01c95040c0d5034aa01040c89a03406510040d8948106180324520582607880181a035200c1e582c00d02c40c2d803021a0b1034212030b10820702140b00066240d40050046913501c58a140c0104480ca004198a640c1d1004070b415940c13035401c1619403040c0020204122001004081c2501500f80055403e500d020340009446a000030000340c10b202000840e9810485025038140350320003085130410500d0b80712408141d40300f004039480c101151440040d6031606003d01541c1300101401e950f589491707410040717248042d4204100c088864403402c14003100598040c0040c5208040000050003040100794000380351140c0038040c5c5050516000060001ca5400811100640e5142c580410700c0e07140c0340c138124541521644414000c5d40b0304018451040fa003c101d0350741c010b4142d4000d01c0741400c54507103581c54 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 19189754 1250 19188504 19188527
    0x7020d0318150c060b030a05010f140a0905060c0705030702040c0f1101060b16080708040915090204030b010e0c07050a03090f090b0a0311060403060212040605330d0212010608060106 80
    0x30554042d264030021381290000e001040000d030030b480c40c90305070b60364180c00d40d25105050100b51781c0712038050816205a001c0c0382d82c003c22281c01400000e0f8079444040d22550040c03c005a65880007a1610600c074040045035100355004c2d0040003405400e200041c0724806000d90740c40004c072058042c2030840c2c5c3c140220310a4618001006241180070303048241218460344048400000601442001c01d0700c01000d04010082d041e0041349540b07160603009443c1c034982e0002d841d028418002880070602801241e41951040e220031a0192107840007901c0501440500400b41d100740c04100042580c08101a000ca07500003003211400f44e00d0b41240d40c00e4505083c3c0c142d0300f01c41b04481c00c0000c44c1031101c009840540240440c1d21781134480d140c0744244c2c2d02040340c1801c0001008140000c1204900c10544c1c48403041241d611000c02485d144075010300400c909003041c0010141c0c1c01072555403880c0030090b05a00801d82c005201300641401d000c1c242d103205408150040100005400d40140e120818 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 19191004 1250 19189754 19189757
    0x50c311d010605070b01060813050115050405010503070f0608060d0203060702070509061c170f03090c1c020f010e1504030609050105090c0a12060b060315090c040f090e010207020d031815 82
    0x746e800d02034221402a8024070444036001c0c001c034104082402031060300c0440c0508180c102c800c0703080006120550300c0680c4001d00a0380510020440d400c0300600000c141c903c1460709010985421000034060b41240c6030182d030501a0300180464140c0000d219000c40358151007000d61a40d911040003145500a076400d2507103080b9218540c00a003940844075007510314400b03402e0030120200c000140c40d810031a0313010080ea0010580c0d101e585411b4020404201300e545003603070300031030369800b01d500c101c0b00703c2020381441503050290700140d4400084200c1595244c4c1c02d1502d80e540c070300b0200c0c00750401c1c10302601c0d6540b03014080f039030744013001c83d8041009101500e003002c014500503084a0115a1800075941c1d00d03900c07075900700f1542d203040045024201301041816803924210400000110240036500041001c2100300007100910040c501151720001000030b600c480341031000d02910800d20000d501113180e4025a08141c0c0101d495821400c1d0b4181125000e40ca801c407000c0c04136100c090707140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 19192254 1250 19191004 19191023
    0xe060c0301140609061b150a0204061b020d0204020a0c0303050c0c0a0206030c04050406030c0305010c0216050d030207030209070513060804020102030d090218010b0d0c03050c311d01060507 83
    0x30b469003000340041c040b0650260001d40b4100ca0111200980d41c039414900d905600800c0405280295105010b0707085041d043c0214505450070001800d215035520f0803085140f40c9142d60070956540b9880c2c800c0290300580203640d00c2a41d14402041d41592540c102c0c0031901d0a400709036088400420340d40000228001003141d004150208110b0340c1004000b44406c9408000205e519201c50090b180210300c0b650480300d4003829450b065082d1504e5400c02021907001300003009491a07401d0b40042299026509403881d44400d080480c2812569040030b03400c5402107090003000c40d4014000d100c1584e161201807001c40e1281e000b22031b072403029140030f401a401400550f8001290307501017404c0500c003c2c00b20324000d08120704111502c409a01c1119200008103c41403200300a02580d03400e410075203001c001500c1e14807040703681c034061100f003c0c5003076011014a001207050350200d0454040301078400c1c041243e490b000e8151a15440102d446884a000e00020308c07240100c042e100756075405064030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 19193504 1250 19192254 19192289
    0x5030606010e12010612061103071707020a08040b0301090b011d0405101502011e0603050303011205010b06030108010911041103040204050613020f031e0c0304030f020106090e010e060c0301 83
    0x4698094002042c1944014a002e1080b8548003d2251800134a500d0b40344400a0440b03007800300c01c890282840c515810300c10410080740b1a070109078102d1290030484a00215140e01c0b10480c82d06a80e02d1000f0f085500c000790114001c900b16014504a5030810070a0090300200350044400168450446c0d14103844e404840740e02d4503290700860351010010305a007112035690003030901c100702161275000141c0d54650a010170f84c01c1c0c8031034070824200860030a0203650b28603621070f6520f100512a1281c400440340300d4008021086d00400401980107101640780e50f1a4085980240001d0308202c1e56580c1901c81196982042d0290403094042c0c40c92082c00c0d07544075024000a0280100b82c0b42c1e0018460000d24040d440300d10140c60298494130302d035903c0c1d19040100d204660b040010541603c0503100c20440a86540c80880354855498a400a0008554801a03001d050030350001010142000910303500c4800542c0031407050000c0b48100d9410f500e480c06041360520082c000c0c84201742004920 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 19194754 1250 19193504 19193507
    0xc080d0c020a0602030f0f0603070f03031202120405060a050106021f020702040609050106050c12091f0201060503060109090302012d0b030703020a0b0901110d09060c020612090c030d090503060601 86
    0x10514003501c1c010b8502201c4655251812039004580600140c414241801740950740c0204040c1d101c0300c190000c040f1907040110614046a55120003010440204094494050180c040e1034071400d00c807081800700e08042c90030503240c510440300b070040d8500e040e0001030a80d00c0000d50000114005031100c00c00b0042e022008045d52012106070381041c0c542c4070015078202a4880c181c000c03c40ca6644d039488001002d10039003131404200785a50006c030284034403100e0340d1750600d04100703a108419010405a21011082e4050100c0307a11076a414040d084c00016401c0ca542c100d40c0e203292085d03000b04100c100d04550400c02404400384a40000c200f1109019911003d512403114210020700300e6100654030b0303000481d02c0740316402c41c1c0c04544011448140c03d5801800344072081300180d0142c1200400d100006142c22521711860302006070040f4034000b50b40701e40741143d00303500c0890203010140c40c0201425075543c80c031152140c000e1141c02291070403d40710310200e000380c800050203020680c642000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 19196004 1250 19194754 19194761
    0x20c091602030c060106080a110906040605070c080307051f150320030a0501140708130807030507061d070f050112021308030403030e0103060f080606090c0903011404120c080d 77
    0x100300040d40310411a1110303460080102500901940d9105829480d150b044403041c2e808400e015824490184802c250b070307a407074906645c2540e207145489610390059040201c840880b13030f03000306024000003401005000003c03481c100c0195415104039140e0a800d21140201d422500c4250000c40c80c0c0070091001407100075282d04001050404038002248040020342030000940c401c48442e950307503c50300d40000324000447c5d448221401d00011030b141c040d18100c40d01072a60001485c1c0c940c0080c01e10109809202511917450708100c0402c6402008461911405200c180b507004130b2040100004801c440085100c0035100182e450404c82001d40c1c034600007942122020b03903190780308018003254610003000548025802a51030800611340c5800142c1158100d41080a408002c41c0341403100ba10002203081e0001d42c15203180340c96513100c4141c5070240c051818a25459420701c03101904014014400d070340120700443c40740c1c3d07241070355a2013a500c805400d500141141c0040c44180b1040030240e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 19197254 1250 19196004 19196041
    0xa0f02010201020c12090a0e010f09180f060b03010b03030306060a05090307030203031c0f0501030f020906220207140f0601030f05070302040c0917010b0312090103020f130510020c09 80
    0x1600381180600403a0a1440304420300b41140c4001c28001d41c14a41186808000c01e07510108c0e058650605c1001c0c0c0020b159801041c4d4a02c5d01c440c0300c0d9190284120201e501241c0020f0751a03510221403400201900c02040910310035820420800d08a242c0801101e004d40070041c0001c5c5050015401074407160491000c481d498001c1c40d4002001d40c03001d1000f04240c00e07129207900f011800c050054000ca0f05819062210f581c900401030000801c40c1030040e02a540403100807009a94000016807a242d000d8100e6040040801c40202c0b08000f0760094243c2e24490710891039038222101946980321540060420a503100b0401080840d50a00746e4402c02c3c1e02500547d41801c0d1039401040503228031451500019080480400c03103001c03510f0912001c02c0d01500203210340b03940d4000003a981c246c0650a1f9000ca04c0000744840d90345e00a0341180da2403003910302501c1e1a080256a04000306030f00384200c9005490582d0721554852010076404031200c0c0090006015031144002800d2880d03090 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 19198504 1250 19197254 19197257
    0x100c0203180a08100504020109090b010203031b0d060f06020f030702060403020906010c05032109030c0d0f02030c0717060106080c030c0306041e06080c010309030206010e04020f060301120309170a0f0201 89
    0xc04000c02c0884042c4038003504c2d8038603544041000c1c1801c0c80010003d0500b0740c44800c0c01441c00f1422a56a030f80070084036009101c00071412100843c0354107000c00e51294010983c115440c00034001040380e00d4070300202c1155459000c1e80c0c8413644040000d522489400d0b4000e501103001c100a00042c50044070075030b00701c1d906140110b0700e90b8031551004e1450b0710120040c00007050603024111841d841c0000664403d82e01c4001d10308021001c100242d03130b15610140030080c00284040c510269100308203840550006c00d046030300d0701c1d43c0d03100d000800210711018150b0b00d018180000c0f98990003020344600070300c42d40d02c41501e5651031b0340c0904826000070306481c0d4040c0d19180c1140d90604a00314254005203c184002413861600d142d00340f84c11500d001482c141421b0030b0f0300c035002c66008114241107030204c00e09400c480e0394a20024601d410b5901321a50310410100000c500000440c2c5184d00546c46034540d6443c040c0c84103414282c04903040204400d0b0742c0148070120028070300805501849206 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 19199754 1250 19198504 19198519
    0x309061716140301170709060b030708090f0307030c0605010905060102070603020c0106030c08031207030b01020a020f030a020d030206090f1b0d0201030902040c050a170610080702070b030f060102100c020318 91
    0x98002e142082d500030390000050613942014141816420311811004146c40f0508200745441c0490340d09031400000d0038482070069110001d06182024010304001841d240c0959654880034600503005541900055070b040e0328250000c209005284121409040f050b002003442c80d10b4940101c020b0b51100c41c640d00f01d9503c0f640c0010002d8201c02068ac00f4003054030107181c540c0810b14081900b08402804e0004043c2070440d424051398011520301c2d0100e40644a4406040401e808a40380c012113031002500300c1e402c0024402403580c08146a401660b80c00d05403008961250415136442c42202c001c100e00002aa40f010301d203241124581c02c190384103060110740030a071600000c0490302c0c0c0f02800b90101d81c00094909a950b401064406102c15010200b1045c0c20f015010811040e002d030400000d11007590b000c035013414000c0200c0340040204c411400d0340d0b480e141c51480c001d407009a61507405445200104034070320141340100103843c60365278003c509014010380040c0a0320748102079140c0129a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 19201004 1250 19199754 19199777
    0x6060a021603030504030303051f15021e0309010206090f0d03020c010b0a060206060f09010b0a0e0d0f0507030209072102090a080703050105010501110a08040504020d0204090c09030309061716 84
    0x8055925800031030007504d8040e01d0751320710304000d400d48000800400402d040000c01000d401c88041e0948151022540315500030b542d8150700341e04d048001d4507040c41048105005500e0a070001004018100e801c0e0f00f65140b603110300215903510800b031404078030603812410101302c0880c0b0a03400b42900c0403581d000406e92071035901c04610410255008600180c006104000c1242022024282250720a40f5001c401d0b604d4291003400500030410545c0c100a000c8020b408030f640c91070841041541c00884c441f05040051801d2960781c4024801207010311300140c0041c1d1914051031021000a004014103c018025803408000a61000d015258414800e8401080c00c100801a68018603c40c200010302941000000b5100c080b0002c0c0d241c08681c885540303000020003010a44044440684000d6101e684c1c600d4000c011740241e0308079040c428544808140003a0340851641c04690080d250074118640310345040b180592a01042c0074800015404034082c821740c036a41c01004142c901d000b484010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 19202254 1250 19201004 19201033
    0x18210c03021f11070f0b010b070809090702070e010e01030c0506070308071107090e011d0a02060d0510030b09010506090702010516050f0403080310090b060405090a09140303010914010512030306060a02 88
    0x13009140c0070b880a9008110000400c222880c0b80b901411000c030000382000d03816035840760640301e81e141c418080d40800000c295007600070040c16000d40551810424650385880d4410b240b030909100907135248100d0400041c1d035003025801c40350003039015510108a5500d081e01943c042c1d00f928040aa11f02c1004000100c0403003511940180b03a42c844000715440e0b102c41411070721805490740400780754101003c001d0043c0d4951044030041c3c10117500100d416900c8480100b441e0710b45500c0075008510550030400703441030642c01103204450403a036046c2c403078130350450884c200d400c2181d02024100401655508160149000d0b0000031a86246c4a18050710ba5070b448503180c0040e9040e10600000c5042030007810000d0040d10034550b01a28514241480e14000a0300d81c90017504505015541d05400b0061141000c3d10216400c3d504080b60f0f96540d55002500c001c00c0311940c1c032500c3d081640004102c501c0d080c100240c0d00e040d0034000b9810758903030030204030003603000c114000150f2113601025401034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 19203504 1250 19202254 19202257
    0x40f06020c0102090307050a050901030b090304030501111c150513020702040204060806151905300105041406030706050a020a060c050307030f020306030714010318210c03021f11 78
    0x40c01c0c907400142c0c50b0048001814940050360b046240300c3c10b04008107000729101d4241e240d044130342160720103400707450b84140d40b4114071494201404079400c00540f810203820103002000e10b030784a1100341140034000403140d0119403008189441420114000b040186465070421412280359540185070901e103500040813a80a9031204010800c100c08201551421984083d07442e40214007161410701c3c400b0303107108010080340003501400303c0030810048421000004890704030003011040c107161081c080d81d600b0302c40b091007114401c508142035640c0c4100c4140e405805140094028451641412401d0b14646c1011802d401148620460480800e08a02070321049442540316680e0720704020710018283e802008001025500400900c1040e45000850008a50b4100448007089100700300403405400015031803d60b02c00c0d50b041c0d1106015044107841c0d210386a00b079081102c500c61a000740c2e42c0c0c1d04c4445004d800b5070061240420035030594032041c006a00e01500010701044407103c9039109 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 19204754 1250 19203504 19203517
    0x120b041a04030c11060313082a0109020102010c0c030f030911041a0907180302060702060c030406110c06160201081f08010501140a0f03060f0f0207030203030405010e06010b0403020409150c0f0212031b03040f0602 93
    0x41c0c0d103c42c441015542c090c405c05a00d846540b0381000c140c1c4d029200a4550400b001901c010140d030f4042141c14407880700f000c000c1c5410014018024900d080302510001500051054030130681c0402003a0054016400a441d1007119407100003d103107160200040354000300c6041e60030480400040523641401d10042000e0b0203680c071201d044142d5548010714102002c3e681d01d000e410200301100303890b25001d0350300740301c180c1c2441d10b40300310303611104c0100764080241500c8141d421181c6001c0303501c2c1019041641a5081411886851a0f00400300300a4040500c1141d03a04645a2824008120306030004002d900400304041918202d164081c41242e010741401d400681020051004000d8207000701d82c900e05084c00113000e194103083c4000040d11a43c40002c0c4203540d140302030800c0001401240702c00140e00c6074104a0007682a83c043c09400c04c803041c00005001e0340c20001a1400032100707403030180d820230b80e4042c1c154054504502482e4000791060b115010109a40300004215000401c0c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 19206004 1250 19204754 19204837
    0x70903170c030403080c070b090f04020309010902041803020606040504080a051303020a0306050103140a020a090b040f0c0903170313020d050f010c18060201020301120b041a04030c1106031308 84
    0x9491b80440601410004e036900007200b91001000b112070b25680d03402107904c421004640041c0e99842d580d401e280145400d010080d0000d04003461038514402642c42c901c042030080d0282d0f221591610104001c480f01110b00901600c41448642040c42c8102c001d001085584420b6655103601d07030300080c1644a06902c101ca1440d200c40041c010008071040030764901512100801d170030b1210b6400903d00754220301400c0d080c00c2d0f035010410343c5940d0303c2d003101010000041c000c103c07040c0c1a1000803c4400d02d408242c84008d11508119035103c00401200d100e15000200246111130990802c500c112400e001a2135520a041c0502c0c00b1603028414044403100b641c41d0502408400081d00500c0c0e0115800354080d64814401006170584146042c0c4000d03a12140b5285160786500d084161480103c641007060441c0c2c13010801050f4010382c0480e0703e14042d0140e16804000070b010018544800c0f1040b1940c0b2035007511034800140171b200540201025442d149040242d9180300b0000c80c41808403180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 19207254 1250 19206004 19206007
    0x40e0c0a030b12150c040b0408030306090702240c07080a030915090c141203040b070b160c1403190201060f152a020603040503090414070903170c03040308 68
    0x3241c1610a1034030b0301da01a41d00040c0d421000d820184c03142c4150707103400c0f42107010320001030044481508503409062009004e5403100d84a8202907030787e4204940f080d0003003030700d80089803160380002a0b42c1502c035210481c410807410b08400345040c03104040d203194490003083c41000000307803011000e807a4a9146030340018801c2c40c181040401c220023086444100c910708080340020801c1d110761101601c0580c00c000fa0700c5c140420100e80012500c02a05801d800089004241c0d072a40400521400d8011400c1e131400d034607449142d01d0301c0740c0c083d00e10401203840c01c02e8010009104d00d1050805803054010b480c100301d0840d10080d0b0000c0c0076203141c030043c1d41d030b4641400400641d503401006402c41d44040c04d000c140301240904600c01000083c03503000200740540500c10701000d0324010300f0f580602015200d08180c9000fa9507130b00101c403824495803c141c0c1c042d41c0801800c02862240c1c5843e62a01d070050708c1c44c0c0f00ca41c0303940450301010700c4054080080c80c100003c01c00052004510540499 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 19208504 1250 19207254 19207267
    0x7120b061b06010b0a090b070218090a0c1a1c06030204060620030406021207060f0204060507111206070309060b0306040f050f0c0d0b060112150f0e0c180303040e0c 72
    0xb42410816000501ca0340020300c50520f1050303100042100780c031544074402c1d0391413149000040f42c0d19500c54811903118145010814940c5020035040f0440b44100315540b02903843e58007d5410401103003e505440c002030244e2a408410000c2d090240303407106030700188036912074011030b00340d070016004880030601a0403c10906c0c0d0702001d102032400001c00c042c3d400c1c1070800c035000351104d500802c0104226404105003007071101c59801103101d50300d59001150798607a03580015107941c0000005a4000c0950307407000c181c0d82007a407550f180100f040d00c05009140d42d200804d400500d40d40b00146d9809990385507410f510b407400c00803180500e004840c4440c40002a20340149004002242030303840740c12091000c007198030f8101d103010340300c0d5108000003159951200100c6d920032010755001c980b0340c10183e40d440008848982030f03040d900090306101c25651603c1c901400303883c0c182c403036485106042141503401c0000d01c1c1000001c0c2c400078107481c0381550300c05030503688020650f51918408400910b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 19209754 1250 19208504 19208557
    0x150613110316020613020d020111010c0207140f0906010305130b19060501210903110307111e0a03081608030f070917151b1602030d0809030307120b06 66
    0x102c201e005610b100428080c40c210400038207040d44070200a00403035a60340c41c5004c580c09051400900300d01480204025100603800070340d034200620400008001d03616995425040c502c90040c3c1c10304000d812174242c0e448410044004080083c8140411315141d06008001015591168000d10210440307507020142d10120000700c9146520282c14850504807401c1c9405000c3e1010086c0e985c031680004100c8503609081d1600316000b000ca030f01034000003e03040201b00d0141c056040c000310643e03255100350100101168850100d012040d0f102e4002d40c000c100091284c00140001e17452480d000000e50303c0d65491807415041501c01d081c00703c1c0d204017003000c1550b0000003080107000c0c40380607440e81702e1740021003030300c0d0000c1e2489e8095040000000400703103802c03440103520a51a003581c10765126002c0294001040c80403030124401d02400007600c0620b0b2086400c1401211444061342c95901c0340602510f19641c01030420b00d02d6512008d8a600b0742d9a004080c10748444010240d24507854080203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 19211004 1250 19209754 19209781
    0x70305120108031306050c0a0b01030b0406110306060d020c03040902040b0309010f020f030402060904060b0c070305060a150e0406060302040204090605031c0504170307050709140702010606021506131103 89
    0x4030410b103600a201c04429120300074024000c0b1250360030710343e42e61001c5454240c20410b942c60f01802441c0504000000c00c101e03404524031581c041c800030400c4d000140200006480251a1264025824004e180c10502c25500031300381d1415507401c4074a020350f100703c5141079070000c1d805016004004010420440740038021100030410400c0118544024500c1c040710178000504060700603000401c4070f451580701c507408a0080e0004158640c0c88240b95418640d80c0c850b9400304813441c0c001e80001c1510030704940200e00c00641900008883d1a06211605031a010020000d45a003500c4640020240e252440144027801710800e01182050400c1e061510f00007007101002010f0600760340700c1403035652100564041ea407001c8142041580c60f01c00945c03650150520240c8030780650900001c046807141d01089150100702c0c0b1120150340c0f03080b0142d080741c880344030300805a0040b4a803600350251306007969074004402001d240c5843ca040081000715440c0c4034461072261800001c0c00760883c41c421 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 19212254 1250 19211004 19211009
    0x4091a010f06110a06020d1404120f02010605090703020705030415090e0105010e1f03060503030d0e011103010b07060506040e010f060302010201110c120706020f2106040603110d0201020309060703051201 89
    0x200119400d20800fa055a83c640c1c6500241183d5404940400010000c0c0c2050715001c2500030300c20320a040c2402c0001d01e101c1143e03c451b000c119540c0403d013003680180039800c121807001704050080c1d5a020016000f9510051080740c00b40010040406c0300c040c01c000918402481e07503102d45106091050207170040b50107810981c18030516044043e45943c03295801d0300f5100401241c401d2a00b0071040c141c010307081c6904180c1d41404085464080d4800f03a600c47c0c408198510000e02c60040700c415191481c0c4828042c01340d01c1305007000103801280c1c054200a40044014100103114118a0849821540140d0700d065025860ba0300400540da0309000c2c8280e192001c0d54010304d055420742d90390780ea400c008032680d1800c04001c01c1c40d006002c4943d0560300501080c2060581d1b0307203080034004000f101c440301c43e244a54040170100c1c6c600d0515115132011340303612409004ac44402c82d02000704080302c00604a04500c410041030755151528006000200d03c29124a030311001e8880000f480e104058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 19213504 1250 19212254 19212257
    0xb040608010f051e1203070602090310060b250b0406020a11070605040509090a02090f0108010e15070804050a0c0b090a0518040201120204090204060807030e15060f04091a010f06 78
    0xda40a2103d42d0303c4000100c01800580c5065401004280100c0d14a80c0c03080540490b6020104180c0244400ca0300140f031110800c5066230100708551050b01c0031510365004014440c9801d00c000f81c4142d240c0c07182d60917811829200304190052030394030359180000444c0c040381d03401c3d008640c610f400e682007042542c010035618041d08449041c0300005225000da84901b0b44120703403c40200d90212000c0c4820300c0703000d8000d00351000340c1c94202410011020300b0701c01c0410720341c40c24091000381e07440451200c0c01d03002c407a400061161142e16045840c00307400707001520980600c4c40c00c207000503040d2540c00001c1c84491841034450102e00100304e03030043d20b644800e00489044039031066084400040d01c1e80681c3c2401c1ca00b140c000c05400000007800345401000d9404d10000c1c001c1001908001218410445039405200c0440c0ca0304c105a04d444031403030516060000d10000c15420316140164000302c1c0000b0f0300000d94100340c0c4d00c80440681c0d0b07007403000d0500340c0864014440c0008407044003001d0110f5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 19214754 1250 19213504 19213529
    0x5072d020112140a090c08010608010c0908030a08060d02030309040e0f010c050705070918060906020304020901060e0904030305090a060501030b04031b03090b03060a03050105090c0a090c09090c05130b04060801 92
    0x80b03000c103d406a000401a612072a920405042005444032004015140c1c5038000c00c8904c1d01c42030341a000b07020409003100490100140007423280750000c02c8449811080d81c40030100d4461f0028485501e8044100f01e13414041445003007426101c1c1c1c8620304c1d00c1d00c000001004941010610542100c00c0707002070804000d410044030020810015406085039907482c5d000842681081444034030a0500b4001440d96003406d950009111144d006140114000c0340c6000c1580d80e90201542e01c074512203503641e04000c4000005010078003036440036070300918000a03105030316565500c04044030340980046840600e078009200c18568071110003d01300130451503103000042c280e00d001e4110340c0903110344d1070329a0001001032415103400c06a1001180e01070000c2c8182d040000760b281d202d40915200b0b5000c0c0300c10b917a0014109000d8014200422103d864981c8214202311909000d072001c2d00d502c40912030100050303810541c1d40d803014001010030404194480341007200040805c501a48000f05140c071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 19216004 1250 19214754 19214771
    0xe0708221109060406031a01060f050304150b01030209060403150e030307021506031f050604050a020901090302090c04030b040c080c030c280b0f040609050303041505072d020112 78
    0x7a04024005850342281c404a081d5581d100090107407016400091581104d007a40020018854245905031040c0340c0340c3d0103c0004582d8112040c0c04100c0c0c001e001c05800200b000d00a481c1035110725800b42040c503016250038000b8000c0b40455000c1e41c0111031414401541200c01501403103034600784a0b444010310700c0d605102d08000e684003456000341400403107400208000f03030b404101014126441800c540c0c1d20340e80c51140c5070300502c4115255400340d4100000144001c8661084409503001616020022401c6409200900000810303a10f0141010480400030624409540d03200e08d10a00300d074105c0d0350070700d075285040078102e0b032405000760300041032805030340c1e40c0400710f5038260500104404c0e044412440000e07821319617408450680400240049642c0200700104284d456548a080d102a40c0b80145a982c1c49180b2a4074136008200011560343d900c01d0000705801c9005a06000812041071440c00d09695502c01c00c0464420b00f41801045580101d103241801030f00308410400400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 19217254 1250 19216004 19216013
    0x9090604020a081b070b100e130206040b13080a0807120306050f13021c0b01020f060108031e0f04060504030c05030d020d0f20030d1d07090f060e070822 67
    0xc07070250124a0184160441c02d0045507044e080d01c9a10b60044150301d034070706010301c4041c6207520502800e007551a05000040408583c5141d56201c0c0d90302605051900e031406010b42d03407642110701407410300310800034000fa0452081003581c10313590088903429990a110f203004903015015400da002450b01340f4000b00304a0391589000c110705103007980e041d6417102040380c06000074410080e081300d05443c1000300e01e0010ba800e9200d800b84000a0f0210b0b17003004041c62060381d44200034819500560310030803083c0c80081415800c80c6030036401e280f045003450808448a00c168001760072103400614041010800e0107003200800740101402c0d000f40c07405052401e00207480f192041c005409019401c0b503107109940c031607a804a03070f00b0110f000342d524211000301a10303240ea102c00f001209150402c1c9900510340051605000f0700b041b410000c1c4207a62900300d42d440a070801d44c2007841e25175591100000d0003814894201e200f18085e540704d140038540380e021f001008242404c80540d50341c0b00d210143c0040d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 19218504 1250 19217254 19217267
    0x3060509100b070206090402030f0a0605041103040f0c1d0a06060f0c0318050316090b010f090e090304030606090e0708010c0c02040f020409020c0313050d030c0204020d06080106080309090604020a 86
    0x2c0b0228055140d5400711030001c100700d803150304000d0760000c1c800001c120744500741600700c41c002c440000d024801c0d10758420030013080d1100c0240b5024005010030103c1c0c000340040c6034031801c0904c03401c80d038401c003130780d40c4445421182c0703103407070f00203a90894010030a415855102d100003400141c2400d0312004542d040051042c507041c2d00080c28401d60f481842c0210382100034080041000400b00c030b40074121204503103100402c0d8030544074040c0c01d1101d5240b00b580100031800448206580703c0f48190b00d001d0360712051303200203444120305000030040480455060700a80028001e00d103400304180d9038081000f40751500701d80c000100b69140000c2420304030381c0602c1550314942c044030086919150803610320000c0c4103552000003150f10000e100759903c54040080c1040002d0003c000c43d80594a0081c001c1e11000700e400100002c0b0340d455000c0051405030b010300706842d503000c000074519403110039160850300e80760000300c007540c004910005a0700e06815403551041c02a01c040d4101521650702600300c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 19219754 1250 19218504 19218509
    0x307090b130306110c010b040e03030f04060f0207030309022106060d05030c01020301030f0201140306010519020c12100f0b090411060f04030605040b0105010203031b03090c0909030a0306050910 85
    0x3000010100300c14441c00403800040d40c0c0019041000d400001e014404552120b80005015420500d01100c0c0e49403034441e10b03140c00b90620155103035039116031010340e920174010700490300103558910300c8a18049501c05482074500c26100004c4040b81c0b4010040c001c401c20b10300700018803008060480b2a200421226000102a038250640c501e0600c5c12601303600492160700304c04d61005c030000041c844c060514202c40350003070b00c0d1300294160614001d0710310f22040750401d0100e82d04200c0d400c050103c03000d18145800340ca10550384006190000200700810a5a9220307095000b01c0c6010f07610406441140c09944501700c013007003c0c11281e008100c4100004002400302c1000d0300714407006403294011108041c102e01ea04907659902d03803038280000c1a00340e90a03592605000000b140070350000049034001e0050541c540c0841c01c1c054030400c1c05170b00081005d029801603030400401d0762070b8000781d54015801c66010f90b417100d42d00400101220103d030700c0355118002c09030522100d0384420180b40b06 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 19221004 1250 19219754 19219769
    0x9090507090e09030c030d2415140903010f05070206131e053405120316140f030711030105041a100f06020c04050603070506160501060905040f0c0803030709 69
    0x10a0780c6a843c1207056001c0e00401c0c80090100041018000c0701c075520020404642a400003199603800d50203844071103440c00f40c0b8a0004489a13081d00141c041d00d817541143c020030822a18148000c00481d0039643c1656807203480079200c0b01805022031b01488400c0c0c0c042d0b44034071801082c07034150704c4605112a415005a501030341c03030140202403000034080340e0390301400000002d03411480c182290660396030740c40c8610500d0202d0a03007c200703860000480c3c942e0b4415039004504100c091180900b81d18001c1600300c610b8103400008035108241485100840000d02d000f954450086061a050202400d01c0840c801e03490a810000028082c007200c1101c14000c240010302a91058006607400030141c100d410800e55100001900a0303000030320030b1a207081658140b0a076150a014140c2c0c1c0d06042c060168480820b000800d80700b0110704040003118040ca00218100f44d540c16020100e41c41500c00395a4110f03d001c03c5014801e1030603c0200600c0d215004524518000c0c80007049883c09019065 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 19222254 1250 19221004 19221029
    0x70302090402130207051e0303010303080105010509010210050a02040501030e2b0c020307170d0305160309020607020910051215040206090f09010602010c02070906030804030303200706020306010909050709 90
    0x1c0a5407103489401148009112085560341c1150402582d56401c0000020701c0c24220507031180600e0307002c420340c0d049030f5040c3c4840042d03908280c019945031300445103481c1107110b2402005035032405401014002d1680400050b07486003414001001d5520303854801500b0390150900c2d000d0200e45550303100d003820411079000c0030309400003000c03601d6480415003c1d40c035110700c4401140102000024800081400d000c68000d41032000d4240c007916412100b070704a02c40305104208035540660001039010344020440741c98828503500203628080b040e65400010220550b003800581040723140e07016008404001462a285015650511858004d200a000b03032804038000200e038540c12640740d1100001072802030340d5a102d0100a0080141a025000501c640d15001801c5407892003004107694110440342e18203410354400b07602410141181c0d600c0118500041041d07010b03154090050f082c0304e00720250703a90400f50001400000c05401c4000f21515141c180000c29070032079031110464007078002c0413 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 19223504 1250 19222254 19222261
    0xe030a06020a09080f0d0305061917030d0501081c020303100302040f020d09050c0108010914010504020c03120c070b0703060e04060903021e01060e01140303270604030f050d080907030209 82
    0x4546031903040e44508200d03c05d484c0494881c003000300e42c244058913a66420011540c0c1d0f50304000e0400070030f8402110b44052034405000c101040f40074012a0390441080f40d15003014541c050b01102e0090788584025001901c24020408182020300f403000c0041c0300031820340c14207402c8080e048040d848000d01c595503c80001503c1c3c1c0d0a074050359904141c0200400015500e41899625100c510b00514000341e103000010030440f1aa00c5881e5101f840b504403000583e08003802c0c88025070222482c49558881401011103000d035160030070313100345904d150144d2209110701d801c680040015146030305150910206010900f10820036580c419000f0304081041015810103034205103111580c94011004005001520407054000500b1034080d00400180740e03a9503440701011407800d10941c0c1c0c3c15001081019540241030b0212074680c0040540400707030020318000114a68030039401101d16045240780071040c0581407201c50001307a50790501540c0c0f0720b0007854182d110030710313408000d00c07440307020011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 19224754 1250 19223504 19223507
    0xd0203090709020a02010203040209010f140409020609040603080c01050a2a0c050d1116080d110f0a14010b04090203120d020d02070606080706020a020105030105100c120503160e030a06020a 83
    0xc000b0a000d810466580740c00d010001d02035070041307600340c1c081c4016000000700c9180900d01c5404690440c40d40224540c0d440e4108006414000d4059032b00c103206002801c802d030b445118000007144650103c40d61092402240b5080da040200714488552900c007910240c42e4060740020f0700b05802d4081c001c143c80380414299094841000003600c60700ca00c2c10310181e031310341210a00000074284004c4a041206000d00464042107074000c00c489500000000c141c406d008403134221000010000344d4040d4241103040c1850300700114015a000d4601031489884000f0038820080030040c00c0d20b09010f410901d402007541d40301c6120301c0c1c900508000941220a400c070741c0c1502c1d41014000340540d61401c05040c001c0103041030b4000d000d5240036506001034140d00004061400ea42e0607142c9a00796072a04041080c54402d914604007403102c5402c000c40040e0502c0810000313038159807249030301ca0a146031100b0444541309446070a0180e01800c85015540000e065281280d02580160b5a564100130 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 19226004 1250 19224754 19224763
    0x2010212010b0301090f02040302030c04050402030f0604060b0916080103080c0f03030c120603030406080c0304060b1002070614070f0b06030c0a080303150a030f020409081903060302130e030d020309 87
    0x100d2503400c0c4511030000c038081402000541c102c807201c8005000107480b512038941284a5403200942c5907102901c01c0340e90341001e4104a9000340018152005140d140441e50b00f0810221b0781107844643e5030070180c40c2c0340b4054066a8000f02c0810040e01c1111003210060700c140c1c010b00010307004500c0800d5001100404028000e24803402d0402d4a8a0b41000a0f4130400741e005180340001656130940041e038503003800004d640403075000d80c0e1104000d403a03002000d6950740c4060030682d0410740f1403141c00d1b4140c603040420940b01d03d542d80184400c070701d0600001c4c10f41c0800001c00101c24020019107000c11041750001d404d1940107201000f43d2348808001900d8840040c200395080032a29000041429012025520a903801049076a1542e0240d0401c0340c21481404001c1403600300e030b2012005410694071441d070840c0f00c6c0000d18034002c020440791540c810209181c000094482c0780500860808900003078000242d500c051000d44618a0360903100c5c0103005d0428075541c1e0100004136100410007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 19227254 1250 19226004 19226017
    0x40503031c0e0a03110d02030a120c03060306111c02270a030b011d060411040608060a09020c0703030e030312040f0804091b020c0f01050307030b0d080307020d08090a0c050d03020102 80
    0x490f4580009440c001d801803040c500c0c00001c40c06042c860307054082c00031088610700b541955601c1da11081803030280b4010a09103509008050382e0f1500400020358500c1021b1000c890048800d0f00c9a11401982907401d610920282c8154018400c80381a40c1d111520f95000000003074942d4011003040000c907103118001d602c0641040b0786140001401e0580303190f040903c81004e4140035195441500707000903903031014005445a80c0030042040214840d140341d07600303c4001880d060b50b0603942c01002d01030780c00c1210f2803400341c1c2003440300b04105a041081c0403d4594190b000e1070429590b00001d50070b15030014000341200c074180345443c0401c1040c0c01100c010b0a8004001c0210740c1c0840010011075440c48204009032050140c13a03012860518025a107519050303649925641d28250100c020b05200c0081541000071001e56a0018115001841c4620700660040488903034424005120700000381c05003010f03411541210340480c0d840c0d06468281d44043d642d2220107030320703031a00300e00920452 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 19228504 1250 19227254 19227281
    0xb0402030708060913050304050114130f050a090510030602030c04080d020c04050f0402030604060b010201023112050a0f030c06050a0b030705060f030a27050102030417040503031c 79
    0x3080041c06030b0400b000b01d000d144152042d041c290380c4d800b8a00d210b01c1412402922541c41400100095845020f900f1240141c12400360b00f0840c0c03110001c503c2c40c003150840c01d903848482d0300c24002030500c4248540180841001440b00d03041502c0780d0300f0010b54500024100304c2d0000006031007070030303100300b00d9004080150441e00c52608610000b5141e00034078000502c00c9050a010610700c0c16030409041c05150004c026019684403551000c0040c0802e0740064199502402442100000c5c15905c42400001c1618881200070014100105001c560070046c29500c514a2a101180c000248600d541c3d52056005071810100c0c10f0a995082806100520f40390502c0c00b00710034001c1c60780200d1201c16098007140c1010b41c5800c01c100481c00b649150440d840001d10005031032005580020b91409081c3d00021400340002e031f0000d02c0c01d007580405030b40c507a40010520040210040002045190105850b4181030402000075201e1041030088503100502c8681c0e070301c854641e0f6000f5404644403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 19229754 1250 19228504 19228507
    0x603050703061b0309030519110a06020c0c06030106020a030305060310050406020c07060f0e240f030f010801020901090b0310150e0306060d05060714040801180203010c09030206030a0f0b0402 84
    0x100c0c508080901000a582203401441030056100f460203800ba00f240680d1507212103041001400d40562111411841403081141112034080e15030b20500c00c108007540214409a40c69510a40c6103140c6000e850b1001d0051204200411000f40c0c045032441d400c070381c1842c0118031929884000791910500b8110304c0322803032814003403008004295000b0b0418404d481e00b03503402c1c1c5a4461040d43c07118400f000c0f440103d807144090464519119080d0321890400702c0350000d00461030b01000c03007241c20140044941d19800001d020340c00c03c0310307501a801005140000d42c1362219420000344603a0340c40c130890032a201c0c00f002141c100181400d86602514020308407441c070140da070384010040800c1c0c0c04a103000f40516004141310742040307890604101d401000808490322184802c403203c0c0901c2900ca8602c4006000105951800303003c2c2c0c3e003580c2c41580c00d501d07111801c1d004240c01c59204414100500130421803c01c010385411043c3e9502401e1408002510300010641401a00c0c20541d007980c003d10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 19231004 1250 19229754 19229759
    0x5120a0b130f0f09030905061e031006090b0f0f0901020a050f010605011d0603011202010513060201061d07350c030406180c0504020304020604050405100e07050901050415020106030507 81
    0x3a554414040444a000148180000483c0040c1150262900a170000303403000014003003802d00708010321071030280d8a00c2c60b0880c0100c0326403407001c0d00181c400780c8041125520802065601114900150540301d9170f440c9082e4800c0040c551900c100041008000c10210301e45045a00078010b051101d60840c2c10740c0c243c515405540d0340200158003134680412010200c0c6403100c2140b10b52a0040d00c0081c0026243d40d08001c45a004643e400c4d900301d0400008006800310407400100f030fa002441d543c1c0001c40c10509141050300d1248140007540360754481d81c0708100c2040e5008507414080320720303011b2801407185080c000000e10201072000c8295260342506102c00a00f40c40300551085002d60070400c0850940f10481c00d0902000d100a0304426401006116034a0291300440d046032004245914180d03070781d00440c095590450b0303004903003110386104204405190485982c080458034109103400400307000a08140601c0c0248540c540c110451408041d000758005c40285811000703c5000b1340c0e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 19232254 1250 19231004 19231039
    0x6160c020d0f05010e010c0504030b09010b0d0c03060515030a1202071a120702070302010206160318080910030506030712060609020c06090d0c08071b090218010e09010605120a0b 78
    0x10340d030104403401c3d0f2a08101262110b410f200d04e05011407e5980e075407400d85562600e941240c000307845900c0b40d560340c5045c08290380d50809140b2400c4c0c81644240000361460130300b14200e5000509500c10302d0f5140d0020103080d42c012401c1181c02d6408000080c00b6003041d003003245441e950f9000100380346070341081824241c0f80d00e03000e069102d510f0211110341d69500c040c01c0b42c0b1240b00c0d2100901580c4a00085481440312140b141036000c10781c900003a1416100340c806884d48140700041d00d1a500004040380c1508141461030400038a41c10244032505151010980c5d8000350720460300d901c18001b04200400a158014070b004241c071003001d42d143d04001450701e03110f890031794030700c8002c2c401c0d50100c0c207906020b02d8003c01829040003600b802c0c2405502d910204030000a11078113240802070b0f009c00c884690b4406010f074488001004a24010014000b4000c0c80100d107420384580f080c1c800411110f617000084600b0b8400411a4400310317210035100030040c00d242040d0a51008902650705100c0c0e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 19233504 1250 19232254 19232273
    0x20312070c080304050102060c0c0a05100f050604110406120b0301050a06050117070f030f0e07031209051801051203121504050f0f04120509060f070204060503070806160c020d 77
    0x1400745404840c1e2569841226030f4070f01c6a03108a50158019200042c052003445014000c140908010342c2c01c5230300b0b2542c4240c24090740f001c3c01c461040d601c258040c0704140511492b41d021006417010049505081000003050090740b1541c41001080c8881c031030040c0039a0408003022001a00a00450500400105c0605114003510780014480d1841c40d081c00764028016009421a84440403500034040c4203c0182c00e0366a20013040f991152400500c01c88108410001035003c2c4650107004203104a0042ca000125800107218805000c4082d403007034641c1404030304440003210200c000744221207410707007107006002d00f10389001c54107400c0003446907043c55020400d0000311010080c507516410303030450151050f14081d032444843c100240004052102e200c0500200d8200031781000c0b902d400149903540410000c031061200401c03600c003107003801d004038800381c01300314054942e1904010606645001c020701c2a600c50048500c02c45405003d028a040700c5d2f0b0b009860300840e03201600308609070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 19234754 1250 19233504 19233517
    0x70b040201030b011404151b030f020c0a0305122a070306050a230402040f0e010207020a090504030212070f0c120c0503010e0d080901020409180302060105010801030206030a090609020312 82
    0x219082200a042c81d45c40b4001d801d0328881426646410141800414840e0105078241c1d0720500030b200c140300e4100d00ca4140311904182c42656010300c1010f50000080c101440e404440e4062040010b0500c006480403908003038820000f840b8a407204070b944403001e2313043c050850f4030b261500c0d1040034840900c00800c120b801d480c0686001d01591b100d074040e540c2154403c0304841154051111900400003030710b54031581007400200082400000300c2c030130300200c803034030b07500504541c0d80002c9150031824900082d42c014020f084080003149440e803000b0707446030324000c842004807900107100410032000208140c4511f42000259030101d460b50707070802041074159070940d0640f56003c0d0000d02460140035140c229551000031b8581d13107142e20b802740c1d01988090a02005950280008280e076000c5204001903002c03d42803021340740c1e5141c28041e09065040c1c024504000f1100018400358403031500b241e13048001315000082c441da0030304002d0300501070b00100950502460480054140800300070344030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 19236004 1250 19234754 19234757
    0x308040b0601090e01030305090f03011805063702120109050402040e0d0e0f04060801090b0105090f0c0a0e040213030c0504150e040206030402030f0304080102040603050f04030e060a0e0402070b040201 88
    0x340d40e21104015561032103a03102e10490040c000c07005100083c0714002510040d0303000f41c88040d4482c442e800090960b15031150600d4076208044d41d80090240070080b1540040b25447e10b8081d001070b0019243c0a224441160f14164064404520951001f64121044008a4010340038556101e00100010303110558050380b0803418103e10b80c10400c40450400b0340315065449008039035181c1028007012580d00a0030a60066407840c000800385028014002d5481c86030b04107100e0b541c10305023000700380040940300b004601d595504210702a000c008c00ca03002030384c0d01e041a030340000326040040c0182c07160014200c903048841c08000100101c0801890590b03004071010f2004145810300300b40710300d100340716619080c848034001ca80941800001150418005070aa44454003840c00c118034642c4603500c140020ba50004081244c41d901d840740d40e400030103807403004c0d04501300790702c00800700814038241520801c1c0000341c5200c4640101061410340c44068400d40d120328641c20060841e40b0212003e0b030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 19237254 1250 19236004 19236023
    0x220309060306080f0601030605180f0307030f05160b0c07080d0b010e040e190606080303011205070501030516030f020d06030807060b062104030c060203090609010b06160b0c09060403030804 83
    0x80c25840100700781040f002c13940000c1c03003180c1c6192102c0d405070201808003801700070181c8000341210f038103014640e2400c000900456648455150080c1500840711184003000014840807508504c4029941c113070703035009000300c649500d4000f4201d0b0180326480c001031040c01c002415094104081d0803c0b040220300740c840c1142c0e18020428041503c200b101d10440d650400031100c2400b84000039103007082e901803600000d403980c540d0462469030b0720030b8001e003415249440220041000c104081c5c0060203003032806211900b014103e80b02c03455003c603810014551510010b10581181d907040e00da400d011000c040c41000d5690501c0165580840003c0c2c1d04241015502496810719808985449181c21030f2841104028400040304000103030048040015841428001c1031050024500924440000e40410f0400144c01401c403045609401d000c0c003820f1100031500480d1181070303103003141c00400007011652144c11036541031169054403540103201040100074180d100c4242481a44201a0301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 19238504 1250 19237254 19237259
    0x906090303010b091306090e1b06090f060a121503150e062403030720030c010806040207020102070e130c1a07080c0a02090a020c0d0309080909220309060306 69
    0x125101d1000b4007408007180020041002d041c248440304080c8802d030500002010394490a0b09030680e606040099115401201c45551014183d2858074404501b110349900e0b000300500410005044588140d2007079501083d0051803030b010326003c41c030f0b1140c0032404105010002a8101c0842c1c2d4034003050700c40c1d11503a0f50743c1d0313000346443c49a00001c9070590001c242c982e40311914039944405002ca0b00e02e44215154040265881c10006403140718492000c02d05c2802d01106034000030342d00c507492640700340e00074491046245d0300319400070303045101941c0c09070b6912081d00041c1d10b0409594007c01c40c01d4807040421004600000e0054802481140b02d000320725650311a00c8070750076610134400102c403c10071898000920030b100900890386d50005840700440690001038900380202c6800c2100c03600061030031164441070181d02c1200219040c100b10107042c0d611865002d010741400f00380102400b2020035044000c3c0b0840307a000d02801500492984114a00100f05034124480d0601013030900201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 19239754 1250 19238504 19238521
    0x2040e031b0601031707031101020a050a1403071d03070302030a0b1614030726090706030c03060b0301090209060f0a03060609050a080a030f030f020f0304050c09100b0315180906 78
    0x1c2ea4120f035000f480d4541103a4400c40d6649456104050840c14014050890f04610000b03001511040e0392686030039032030b601d0f45c100140c00a890310000640d401c0b002c00070003690310b421205c4548040c68500001c00c221400c0e2010078540700302608080e6040c0700e0442c2a0040140c6800c1681c41280b86d071341110b80042c41242d0a84001700f40041c42e00701000180b0000352741c14403c03c4a90000383c0201c0400c0748000c0300c04221200c1032820b48003103819401110050081325018002c01c103411200d072804100c41c41c5044101c1000d8041030140b02d107082d40003d44401c5540d1020140c40f041503041001503543d0000800107002091140318100114242c0c0f0000039a526003100030408403141d9401800400e0390650701100d000f00c02013420024107940301c48403590a0303414030103007903c6410603690981c7d90400341816032402c01a91000c2d446018a141081022290034149100302c440804140380c903911800d025650101d0000f0600d078101041443c02c1d003c000d2080c0e0041d010700302c03c2042e2071041d100c4000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 19241004 1250 19239754 19239763
    0x4030c0503060f0103030c030203042106050c0c07090905012409060501090501050a11010603080301080a0b010b130501050c0106050613030605090f07060f020f060405072d0b0d0902040e031b 83
    0x9140e900100f0101c010408a030003500040181c3e4400d00c181e0341381035203400f200f640003074401c00c20782c900070103c0d820902001810311840d500484420700f400d0a0280c0350b51070a0b41e903440b500a2100103070301c0344084000c00a003508810f07821500c1070b0b030b4080300111aa5480036017002e035101d545c0815082040008e00c1d035000d025101d05640d8182e4680e40b8180148806640f4003c04c0c8101e903038a5907035004000040350400340030314040e02d02480a000c0204043c14410002903043e00000444402003000c00b4413074016141c5a007c8a03020700f07105480f0b504541c5840d0050106601141d008440040d042d80090103500046003070b284209003c01894030707251484c03540c550713a401000c07845a011440074082c02d0f0207440f04848103100d5204448800d05030000b17560400c3e509903006c4816a0280005005154050b105280081000c801041c050b0324502c0042c0d109502c144513a404000c000690414801659084580310640107407003400040b4440003804c0e500d034009880c41112420740704e88050941030114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 19242254 1250 19241004 19241011
    0x70c060309110d0f0c06020607030e0106050a0620030711040c02010903080f0a020417030a11030a050418020405120c0907030204050607150216110a06050c03031306020903070b04030c050306 83
    0x10010090490b190003480308808410078141e03505002c2a0b00d040000301c0c580400300140402c0d5015002e6414600d01c060113850400c5500e130342d213074103010050140d5124401440210303181803602d040c0100400c50075040e02c21651a4005050000003100e0b000d104c10000e00e0212030a040d1801c016520040608a00301d802c3c60000400041c40391011a048800500507950400d2410b20010f203041d40c3c030b110605812103200c0070050150008901d83c85e90b190000b120b82e4511307240c000554545152240018044c2c8510702845848060384400c2810400e5694183d4000e41030142c21103190a0f41b00d0b4013243d0314001c0d00341a238800c00c0c04c500041d003081c2c403a00a0350220340012f0075031804c0c51403a03501c8064407000c045000d420b250342030050681c920103d0540464540c0a0341e5021201204030003806550315480c1c10001c2408000c00020035100e0740001140e60050b91039507148040301c02403a2502c007920540394035542c50310a942c030100d407081580c0000c100b203c0c810850050500e81c2d440a058640301c085 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 19243504 1250 19242254 19242263
    0xb07050d0f2f0d0905030709050705070b04030311040b030f0603030c0304030b060d02041506020606060306090f10051003020c0106051525080a05030106020c03060402030601050f060f0c03070c060309 87
    0x95500281c07502882003031a940002120041d10340308003841c4003e15003801014007000080c00d1450400a03810240096005006036540074081e501c0c4c5050702801c00c0c411020000e00c150720502c000b80c10700d4441d9002d408294480e0103942c1c0da030b0395a0700c900c4030907400171b030364090b0248026004250546000401c8860100f42c03d0083c5003440d01d1600c1c1c0d5204e49070000c06140d04151071481010050307541d407007441000f101041c8038007299801c09800a180204c0108228080c41c0208280802c6640300c100541d0b000700041540c5220350364281e0040500301c083e034003441d0803070b12519007000000e070160090001706003d00c00070031250741d0728000c1003807400f0103410b101c252150421074006514000130205000b0180c0a9403860400c08075650100564440c40906002820200051010030f6042c00403050b140400c074000e250b41e04198000903164481842003c1c4108020040c0a0050b180c04c0141d9441484c8100d5079038a49042000c0e2907160341c449041200c1a151100021580070700030311030880b813a07401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 19244610 1106 19243504 19243517
    0x70803040611010c05070f05100504030305060f03031e030c040b07050a1502191116120201020d050307020615010302120717060f0f060a0504050a0b07050d0f 69
    0x1000c1c0002e0159040c190b40c03900340d51340841074075030107600688003109440f05031501a1038161307280d00d00c01150313003401c04001c203040c1c1580c4042e200c0c1a00740c662170126409101007580b0703845441505680f45403211250042103041902a42e071102d50030b15041d1501d0703200c140c8401150014081161a64490388a41c03003007144d100301c06411144400815800c03c035810301841a02d002e420000d20420622a490401e5007008218411040000c01c4c4030303442a03134444a0103403000360310202c164094031910403892002880f91045074441c0b000c5134080c102c00d840d05000110345110b08801c00c1e040580900801c0600f4030042c0415000b1005038480c4495072040649109201400400c0c3c02d10031030400b002c2c281c00b61581c50300c030051158102d400980d0bc0308248000d5a060149401c000d40200c035031100459140c401c0c10040140d240214200c40c05019011411140010715a010f400050785 = true := by decide +kernel

theorem cover : BRFrame.Cov 19064754 19244610 := by
  have h0 := BRFrame.cov_init 19064754
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19064754 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 19064754 ≤ n) (h2 : n < 19244610) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
