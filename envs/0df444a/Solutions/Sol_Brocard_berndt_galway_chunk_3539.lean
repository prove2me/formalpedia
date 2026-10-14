-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3539
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:57:00.233289+00:00
-- url     : https://prove2.me/submissions/99d01883-ac0d-4f18-aa31-e416fbc40c4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 636330935 ≤ n < 636510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 636332185 1250 636330935 636330967
    0x190611070b060a080a0206041514371215090501060503010306050901051b09130501120606090b0102060615370e1f02030c240f01140607030302 63
    0x5a4890358244040d4036082c820040381030125849440c05400103000c2100682d2444100c50944040c0e052070b101c6071a0340c00046a05802c90090982c0f0b6850008e41d04102001c07a41a2100560303080035214188100207002c03810000e03040481401180c07015240760140142d1b81c006510080c051029410b8040e17582451205551085e4407540c0443c0d00040148140103450080903405550100248014280003581407425188604002d02a01000c41c40203142c1e40c3d1080c55070181c2c44404000c0c440fa513141e214070030f46040b0301d040c11202540390500c0000d401403203009102558a0503005880c00c0c1d620001070000702c2c0351002d018610010700700040400034000110780d02e001400d00303048001c2c1034020925041041d00c15040942840989030750f40c40b255490210102c0c00750550208200c0c10081a80c0603440c50180d244013010714003425100c00407142147d003a6030b005000040b003003601e80d1a00c0741c0912680c0310a00800c00e401814144840781130074004024005144207190041c1384c424000e035440e2003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 636333435 1250 636332185 636332197
    0x417010902041401032303030402090a0902030a0302070611070305060705070f120e310b0a05091501140a0e060a050d02210601050405030c0f04060b0705160e0108190611 74
    0x4070300700440050041c450284946d1213a880c00c1c00386080c0d0454100b02c4281d0701d000082c0300a214030f0301d00c0009803c031350301500200361203a0701a00f180c5021901d0700e80030f9159500f5001c4c4500061540c55008141c40c0b000600004030790f0840d02500058440780c604407000d0380200000e80d03c1d03526652010000403407000c0802c0407400141c1d254070156801030300304840200c1101d94000300d80b098000e4011602201500344112052500b40090051002c00110341280e0030340d03002640c050100002c00c80780a061030300d28103410780c09031b80380c120145546c100d800c07041c001d90090500003070380703503007140c0c00b906082e4004d000c040c0e07140c20036505100310303000920241d0740441c080340da071018104800185560301a4085230008000d08009080508041c0031980d00c4c0c0c5088641c0344900103090386c04029880300c0e80300324003400c1c06440a9560392901c4c01c2855880300e80b03c00c00c0c0c80700c2f000014001800e0b5600180b99068030160703c050480d46541581c1e4030040e0070140c80c180c411641d9501d82001c140e07060001844 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 636334685 1250 636333435 636333461
    0x15040807080c0604060e0904060b060a031e0c08070f0201060b040605220812090a050301021209100515060711062b230a020d11040512070308041701090204 68
    0x80d40e003449006814049916803440c0111418441030010079002814926a400203495262060360340342054005860010340b0345411000004056402030b515400090100781040112400c0c640f94a034002c0454003a46446d0001034800d20100321218071440c0050f945547c20310000c1070b000c1c0c44818010b00351b0311a601450101b031002412080ca16041b40a142c01007211204c01a000d610380f64100c1d45841c1c030103c0000030f06800140341800745c2d540801100150030080c0085403143d640b140880644a4242c2c0c04882d14030074402c1324110304003036000b498031910418a014901c1c00c80a002d010302900405012100521510300e142c00b00d4135800301400f4001c1c55004bd0803c0c60030000440118181c543d906030700454140742020f25824400d250b400003400d0342524220b180d0ba5004d8518000f0300031007a500100c01c3c10902822182c4030481c000e04240c58003141e48900c140403000d03030030360b0b244d100c0e100050100d80c09000421613203170491500403108949200114420744954001011a03041c401840 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 636335935 1250 636334685 636334693
    0x12030412140c011a1815010c080f0304030c0b09120a140c1c092405070305040315050f070e0907030b030a02150304050d020a080913090b04050106061b030507020906150408 75
    0x40c1c0303458860a0302040c9134045840ca289420300f281740e00304000b00806c0040c1803054540050040000c8002140c00d18005002e0194807800c05203401000688070180648204040b900410140c1c0004146c100e008413540030f1462518005c4001510900301c511050300b124039052000407400715003400800d07142d8410900b41d0041d0688280040c2c07003100c054020700c1d0303155114807801d0680d0545a1804140c800c16040c92a210380d000d01d0121018801c0b90001004440015008080c0400682089000e0391446140c0c00031681c0d030f8001107034201c0c1891001a03000010502041e0b5142c0070f94000c0f281c000c005401e2355445100d51b00428517030030450304a0a401c0c2c1c1c00004000503c90180410f088511092014040400e007944691070640128010b542c400d901540d00a0319002c2039038400c810b0365a000380c52020510301420414001d280a02c140030101f0040321864210080001d40090480d0f415140c0a0405c0419024046000c3c0001d1110b034200d200d0510400556040700054001801020300070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 636337185 1250 636335935 636335981
    0x2091006030c0e0a05060f1c0903030606030513030e030c271e0408250f02030607080c041e03021809010e03190f140f09010212030412140c01 62
    0x6040318100c0c0240410040c1001c400100f9984051204007101c8048452903140c040e90b00341c2102511800c0d01602071200a81e01d0092503404a4000007145400707500c0c100200b41d0f071401c1c194140c44040703c01200c0510606580c40000b400703485840c1034134001400312419405014049444a40c1c100e2512960307210f01380403000b11451a0881c1a40062106090f0850606a69540840c05c0d4050001898a4008260800049901c00d14413590440385030920380004010f090000040b0207902c4180d009005140c0014000e0380a900380714003450015007228901840d060030050400e44081101d0003a1158450005c00350b0303904103480420400b2042c0000190410300ca1560850b03d03c508100c81c035420034003c240200c04246051008500a8100710f0001840c003641114144518030344a403290401186c400001039035900940f00080080e002c542124200010002d0300340800c4034000c0c00c0c0100c1e082502030f8640b25401000d585a400080d2a05058000800783c0c01d6400380403440048142400700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 636338435 1250 636337185 636337187
    0x23100204260106080c01140c0d05040302100306050609040f1e1d01060b09120a0f0b150418080702010521040618020f100216170d14031b040302091006 66
    0x300010801d201d100800101e4501070403a0340ba405030310800c0e41480701d01042d03c41c0365803140c42100e0190070103100340e45282c913200c1c030054501c0d002800309074040c00703480502c800441d000307100301d2050b948001d202908000354101004090801c800402d07a0981d00c1300c025990160030322207881030f00e800385400480c840140c0e10180103151404048600303a60f04041041290301c0100044a4400d08241c4000924900c101d9196142460000b8010401082000300b0418807603401c0449015040219420903151940f904100580344192450980070803140131344070000b4054402010f8413031040c1415410840e0081001100c1d1315615243ca5a10b501c0300b0800c030800406100d4255585c485100c2c0d01c01d15405900850900c2d03441e41a454050350f09148075501041c002c021400c20387d2911507034104460b80301c024210428940a0641c0142c1c4188240c03440c041c1c0c0a8060074601e4400302d0511411980d46020501c0010002c80320756901040811012001d0307101c51a00310301c51848408100340e010b00d401c030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 636339685 1250 636338435 636338489
    0x501090e0f03031b030c040e070201151d010b07030e030604050304030c05060a0815010306180e0c03060f0a020a050904090807171305280f1e0323100204 67
    0x4200701c0c00c0e4004000b0050744e090381e980724109240070500b58944a6503441d0800000d845a5009a410075250104001c0340035815048a41181002c41a80c803141c1d0740d846c403080c00a030f82520003190381c000c05001480f80007103c001a2100a0081c0f8003107422650010202e4100b001c00c0c0c0341503a136034000280034030600445440c003100401e820b6440394a420b481c041c0003400c0240c050801c104000c1d844468207002d80c4240c200001501d8460f2814a2410010101800a0411585040003806104600006450041840352203600903200d0079039156680c8107040b0003540400424420b02c2028003007881291128428581024800c0254503176a080780e00345540f03901c8910205481111041040c080d192040c0302d04482150b5058980e180510140c29481480c00c07030030040000c003000d144c94005113007200d1220030b0702101c4241109151640d04c42001c0d03d840d40c01c60001410004600e040070b082084410400502d507c2090141c41c03a0580c80143d01090740d00a500c1a041c3d203000001e105140b044802c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 636340935 1250 636339685 636339703
    0x30405010f09290c030c0703090519140402030906060105070f0c061d03010c09090f1107081b03090a030f03180303090f0b0c10090c0f060305040b16140a120501090e 72
    0x102000207031038400007002c018400104841c9a00746c0118034041094010817150340039110007402d481d1280c00928a0592001e0140b180b178910110601c030000749400c00d032085034006c00ca000c0c098685661800010b48080e4811281100d00c1d00d100380c1e00341c010070120721481d030207081d05075100041c0c0ba03014500c40178400100705050b442030345425010360f64260001107003000c85520a2022801d182607800c101d00901a0402148200740009802020051024000c10f50051411900c0601114060069949001c1c10a8880c1c2240400c0c4051000ca0b08039a80031405522928000c1014444ca0704854042042075100320045010714005101c01400e11501c0c0300600b003040c0c10281040190650113964101e0196260b41556031481c11f441400300c1e01204501619240241c1c080080e0383d110b000f8010801181e05031081074042c40403907010001a8010300003201c6e1a03485c0c000c402c002103c0d02d07466911000d805024080a006440010702180c06050f0081820403c00540c0d10011014a42403540e00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 636342185 1250 636340935 636341003
    0x314030a2010110c0f0f15390a090e0c070317090307050d020303090709050408370c1403041811040506070f35030405010f09 55
    0x2840340d01003110006203804102e0000180441c0224400c00041e800340328111110059010742c2403800030384140000d401440084140403070700e140900440010038440b0075a41440e40818004d018007610011121050f00b4995512040001214483d169045644440e42c0200418090311080001c0c02840b1501a0300c0f60b141080c130342c500f43c0e140c0e800034140e030b802d00c80c8010040c5200000c506494810800d0300c074a543c3c8071040700c614940464010b990303a0011100c049891107894404130346800d0b28024940a10707801100f1900303100c0580c1c0d024625041985d44c3e40d00709c0e0300100c000e01d9080c045130303004480071b800c80d00d5501c2114a2824880c5452210344681c8040354401c000800a22070100c160b0200700480800000d440704460710400c41078811980000c1e44a030000c6481001d105c15041c102e00c09a00c261a16403040c0865850060300c40740505840a00e00c10544100c3d02003014100159400b900c10b1000007206000c9020080c2140c24542040d20041009084482d910501800d25040c207088 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 636343435 1250 636342185 636342227
    0x1409030c0a0303052e08120403110603041104110a03182d050a0c1404110412020409050102040f05090c3f0c0d0b060906030106030908040314030a 64
    0x104500d556440030010010b0801d551400001c240c481021a070040841405885488a40f0200c000540e2804140691501e600440300c905480d0380418040b1400c4951001410411943c0d0000308140b41e00f0003001540d070080300003d0030704595198856140100200c01119480310106c520050855001d040c10b4454406244014400300d11107500100100c1001c51505141035440041c040c402e00500702d00400512841c8200400c2140ca02c49a01c199080c8000e803105112164041105a85105049402d060741c104801d000000380358203002903840c00940003158100c45c030307a00e0a08a0303005601c4008042a003040030302c06031814110039600811001402c50405455032804407100d00003807922002c030034074049103c50264501155002e0001d51401c40d21941c50190000b03403203503001055200c085446d000300040b29151901c107443d45503070f003e820700341983c2c00c00c401580105185070044d80d200300c0a010000002d4a24014584461540c4003c1c640301d000481c009850f0102e2a001800750341a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 636344685 1250 636343435 636343447
    0x4050d0f081b0f0d0c1d030627030f0414041401030506130f020418050f030715050402060c0a0302030409050c03092a03012a030b0109030f0c120303140903 68
    0x12044555034800600c005035582c0c1003c00c403606161155007890220342d0300f04291028141c1c0c0044821040c100080c0301011117111107010546c40d407a084604403025041010300580901c020111240c1110040c022285003d140645000284e0010751047d2220b01c001800c910803420076001d207840e002001e03900b02c401d0354196a80d1a48902c002010083e00300710a0340703458103001042c01c1c00b91503282c020f8004c000d90707075020794001080781c00b0b000280c0e51441b5070421000034200010403100599004413403903141c4500801d10314094000580140c0c0e100e001407226100b203800c288000d03094280329400559513140b52881200548030001d140c90a031540520401a030f80c50085446148007192054011215004c2d0b40c903078100a150f19001a0507600c0d10400c51103943ca0004001c3e8004044070074080c03104801c0c0d108070195003004c0200b6000440e0440100000382c041c03a01c0a85143c8203007400c6000b503440791089000d41821410584c0007941751044000d591024240582d08441c80001031403a0003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 636345935 1250 636344685 636344701
    0x2a170f0118060b040209120d02010501050102030c1b030304030c06050c06010f0605040b03070903080a0923210a05060a051e0417070204090605042906030a080a1704050d0f08 76
    0x418541c00151042c0d894018010560703440c0d074126410180001d00303008009448882e9950390b078825540460140d8030707140000c10030f0740c00007041d600001c01d00f500400104500e400d800b60510070403c003041d0184418040400000d15418280004e000346581d081d032200142c400c101e140081c1a40a884662a100018440c080e8000708a0381903070a01c9860a41e030392552042101d400d10240e002924068020440741c00c0c01d9031144000085500e00249000001700610b210303603985000302c045940c0000c07003082100580070b041c0d1420400d580d0540980d20405555101e89051000c2103c94601c49581c1e28104910310005004640d20801702c401014818503065487c0c044085220318016806036011880c1400c41d9143c0c3c111103c4c2070703070014041c804d0342814a0106214403a90903032a4800340010f03094141c1c50141c105240c401d150040003441421020380b03030911140d00050300071041000d071403d0703010210440407215008510400007007035844000c2900801c1e19000c004400c042154001c01d2100300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 636347185 1250 636345935 636345971
    0xc09032109060e060a1d0315190219030b060c0102070b01051309031d04150902091f0903020108040204090b100e1b0910020f0709060816080303042a170f01 68
    0x20450394100051a060b07020000e000d020315450007182d00d80300c2c4420703a401c00b501a1007664000c0011103940a01003c01e80c0c1c1c48416400344922f40140c281664042e01c03a110311036048403060000181c64145002440e080d410309990040741d0546036240c61030010801800c0030390a4071040e0103011070401003101039541c014081c102c06452002c02840b051103600d9241c0c0c3d07680c088940340000d2007010b013145030380c0c20114000e034010204103071041800c0d840201c9816510310280c244900e4a55412000c107013164015034003900042e01c02c0c0d8205a550807039500080c15005010700a40c1001d0140c0100341c41c20704046014140249010b002440d0384003005801d600c41c10a503443d501d811182d4034a80860035004038500940b060314540036202d0b201c000135206105500c0041581c66101c1600c401c00c0040031050b15000c500e101d50407540e0b008000103404221810380a003548061100444190030342c40c1c80000403100304c1e801603036040c02188020000880c0400080303140000034402401000c4c001d081074034036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 636348435 1250 636347185 636347197
    0x90614031f1205010b1f2304030b0403080402100e0d03050c10021204032a060b0406050a06020f0c040506030a0f0305040909030309020102060f0c0405040c09032109060e06 75
    0x554000d500c0800e58000140e10704002a040161108480e0782090405501070480b245c002401801505186540001095020540c041031074031070301d24003112551108011486c100701a404c2810512010001071f50742c00c0b015025034000e0752844c10600301401003003500c042240c00c04041c002c035403855041507122480d0800b074007609420540d4a913400d07010280c0c1001d004040a03440720340700152000c80d6440c002945800b50740a94ae0b080500e2000c1e988000e1105280951045a0360145030b000c80054040d400075512000c0150003c1940c527513034030106414000c1a08110056081800d100480c654200126404500119828002410101c1c04030307485010a20001d4203000c00c43c01c10728245802201182d0080400301310820800b42142030080080968240481c014021000819004941d0161880c003803c50600010b2526143c102004003e0514400300420b0182c1c1020020108a00c00c0524490410350f8410039014003010b07200500d1410182c00c0711040c458603100a072000c2d140e035010340754 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 636349685 1250 636348435 636348451
    0x6040905062107050d080d09140d050301140609031501081b0301090c090c020f060c040609140109140a030f1b060f0509040216291308120601200d09061403 68
    0x901d17029401d014080384102803058440c64280840c060400c4610110049110080c02c240c40b40c018003420b0864603480203204a129904000c0c4503022035183c0400103100c803100c02021900d01c000c1a0706c81444168099002d0f054640010890b0100c018810f445404441021002040b02c514255152102c8603018007403285041d036501c0041d5200c60081000d000c000c0400c1e13048038202e1800340490065a405401088002a241e100c006072501c0d145400441c56003058646240090510701c044040750072000a160744115405000000300c0e09200746d4610041c0241071500c045079131010159035044282c0d001170100100041144107a540c01000e032094400101d401595810240200100006458202a0030200c1813500e0500226011400c12041c04c0c40c002c404a00d07030340307021482c070750358140c004060301100c1e08000818201501050603588148141010f090440d1f03204044441c0700000b1820700ea156228a5444a030303580c20000c031344004e2143c1c0c6840003984040c62000c3c41c5901020300040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 636350935 1250 636349685 636349699
    0x80409090201030e06010f06200d1101060b0409061a030c160503270910060c060504170c03071b0f03060905010b150a081003030c1704050604090506210705 68
    0x71684a50003425104035501d08403801c5517110140b80000142c1445181c01107044502e5110004203a02c402c4000910440c002e40102c484403c01a201c031030b01018240895540ca8001080810f03894002d03002428541c540000c071103044c081480c04046d01d8800f0440d07004014020440c20140c0d5401701c44d00c42880c0c01441449011a26010b482c41c05411090300d40300c01400001c03060700c541181080c40d451402c96032420300e42c494003580d1410300e40d54001d10000a01980f15800851050341040b500680f10740d02d920081c4400260316000c131f40100709070b0407083e000024924140f02c2da901040100900c1581c2c002011071605c1e02800c016055448000c00301c5880d5035002040c01001c1d40030742e0012102414109000d14610319400c90b44c3d1011581601241d2640f0109803880c0c0314142103404d60354140c945580c05031540c0c8540020382181442c8042c00c010401021410307440f56400f400003403071802c00220b000c0c1801c6041041548030344144290038080e181e04a000c241c00061032404880c03061304c3c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 636352185 1250 636350935 636350951
    0x2107060e010609020d0b0d02060d090305160c05130b010912030e300c060a08041707060c0908010227010201090828050f0d0506060c0f100c0309080409 66
    0x4000603051541000c00e080d440c140002405180c5038004100c15071209000300002c0300c1c40c208105482c5045140a90002000e004022003081c2d55440070304818002e0a2480c14008900107040300c2482041c13084a01c0e40e06100108128105034044140c0c140c03210006015180d61513000800b440524403518045620940000084c140036140e04150044040c052400e40401c205c00044550f2034286081a40c1080d007004003018500800d540703440490040c1164038010810104036491040a44156580070f01b0200003500001100d0007048420310600300030071510244a4042d0294125910106050340100400b2002d04942900284600302c0440b025820781e003103c0040780103004800006007402c1d40001da5030140300c01804c11565503508070104140311041901c0072601d6007d0031340c0441d0210707401c3c000c0ca100b490302904801c0d44142c002d0456410309030b540b0803035483c00158030309440e1542c202d008400820411405544e2000b40c890034240003d441c10f0769480d14906c194426189516510101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 636353435 1250 636352185 636352193
    0x307180b070b091c140f0d050106020f0109030518190306090320101e0e0307050c04020a0903080309011811010801140a18060b040b0d18080405060c01090204020c16082107 75
    0x186c3c0d288840d140390440d06c1d141813080b0748006150a00941c80548a001c1c8a2005068140a4188540d601da0741d00c0707043c9050844001c0d07441010f441542d40c8440311130b0361040403c0040c3d172480000c41c000c58000c25940302034140580641080c5085060101e2030040440005c1000100c1d134680b08005040040c071420619051340c030014614084044d041e09181590061130800009484214003070000c1c3d42e11100714004200c02c03403107107005800204000c0d0500704041104400603541c054501d20001c903845205400726114140314030030481e0610114241480b89507407040c0c205015101c1c1c140540c00403080200082c0e0203e4803885a030300305090300c2d08043d046507032a80042d401007a5507001552180d858108030b12803a0040d0005d14002490301032005100303441d00d240c04503680c0d00b104d00340d4980b0b401d2406005043e0b001b500040e1207592100c94882c011303140c520090185003002e202400d5140106808601e0850349580b08901c25800702040c05c1c401d06045514070394100c147c00f407040d0b071541203181c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 636354685 1250 636353435 636353437
    0x5010503072105072001050f040f060f0213032310020703020703050307050a1505060d02010516020a170c03060402060912071d0f06240307180b070b091c14 68
    0x50240a00ba04100a2060030340c0c010001065074060644000c1150090203103280c200e44c400c0302e110001c0e122050104021881c1042441e14282c0120f0012030400341103e0302d4002c0e6800307107010600d00100b8440810502180d9045114401e040b0000200201d038003000d800d954580b5101c494001a60001e05c800815000b00300d080015940302007625101c14841c2815500c0c1d8050b86030607a101c1d0301e42c0c010803180c6c4841c1c0c401e5500c1914024002032428001d9001181c10303420401c040ca122a200d0b0713601602503919140301da00141020385903c81b0755040103441c80d00f090030b003c442d54041d91080e0f041c000144e65a07020703213090003400e80d0240303210405c9020580c540301d602c0e4043c075902140104a22050442011003030312860810032608800e072281000d208054200300f07001414844540018280f0310240740c020764104084d071928000362000202400c203141c2040d406150b12000001d44042040100040d00354004031120181c8000c240a504800f00c0c01807065805040101d090140000502d01c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 636355935 1250 636354685 636354737
    0x509091b0d06110a0201150803030c1e07111e0d08090a0e07090801110306010f030509030c070e0901150803030f09150f06090c031b0d02120c030117070501050307 71
    0xb8038103100125200007204410380c00a00c0100055090070b0b00d1804c03081b4000c010204580b800c000440c035580c2c070354141040320b410241c02055610075402d6113800300c50b80c45028120301d42c003c0701107801040d4410704205802c80c891610300b00120040e141100c16a0b101810b030034110390060401d0341d4418006000449410458000180c08a8100c0901101c65800784001d01500c1400d0002c0001e040546d600310007a0104468442c0040d0806051505261280d0001d6401607284400c5a0074000001da0541c10f200890700f051381150007100402800c1074090203926a01c100b240314001c0314038280f150090b202d104c01072100d1203407103112001c81e440f0f40d0104110b840390352084224100d9810803c01007141881c042c0c400600c5884c14001042c44800c450302100e0107900745848001c1d02c903400b601800c256400a03a00c0c0d0420036400d118281d602070350700039000d20820350b40320f0041e543d40c101114420000900d40751000b255000b201d00340010798104080303a402081e14104410540240c0200c0d0a40c11840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 636357185 1250 636355935 636355943
    0x1d0607021518030c10030b0301060b1c060509070c0f03020c0d0b01050103140610030908070f0b070801211e140616020a020907050307051909030c0509091b0d 69
    0x1228000904190207014016840c45007444031804900841010303551401e405074a640440c150020740b144c00d000758030200f46d80710040c001041c46036541d0311030900380c3c12028105038004601c003820b03c0341071101d2050802409003141c0d02002810111001000c44000300c0e001000402c603041801c040c14020000c610031104010b001d43c220a15515090101c1c41081c4030301030200b41020030031034441e042c0080040c03280360050003030b81c030300440c0b00d071700f00c01424203d103007580d00381c10800c0045c000c01c0c48695548000381c0941781c41c201c5420034902c01000004160303c902800082d502c450400d0350402400300c81c01c0c58010400240038640c00308000320949c22114001c060b07004e0480000018600404d0080c40340030012440c80006125038010798981090400084d40110741000007008a07024002468021a0629025040001e2114401f0030302401d0780a003008603d55900400030132035030707651840142a0996000c0e1321400d00415050b590005071700e044036503e26410550750765444110720b9034034003500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 636358435 1250 636357185 636357199
    0xb0a111210031103150402090c040b03090601050a0e09030708030621010902010206011703032d0708010e131e031101060b21090d0518090f06010206070e011d060702 72
    0x107500d14038074119a00c01281e1900c1400e00100107850081680c207610100c084550119aa55900304103600344000c0814404400501000ca50001e20703202961050800c10004d20385941014200321201c28030f58841507261011004110118101100b502d0040b64084421510b83d100c80001802000280703035a13902501e60320300304c80d8007454150030420006000782c080e584180d8941040c00001005803880c1070141c1c1c400c1021035202d02d16110020842082e80501c3d0f034015001400d2809586400d45481c00058031010041c898a100040c210350844185800364000e0320307041c0e650890f1028001c81e1150300340a6550541c06041c0a016604650b40c40c0320000c05c14162030310010042d54005020700c41c42d502e5100c2c00041034001030100c03e4014402d2100810300704142e80000c40b01540040c10792a0740161050301e25016031190180c1501420740420b08042502c0c0600c002440c05100621601c01c20140c3c9000c50a0390740c215000702c80391040088481d00c0300c00c061001c21882d00c02c10400a41201d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 636359685 1250 636358435 636358441
    0x7030f062a03050f0609090a02240c0f0d0e09010e1305012f0c070e0a0b100507050c0108100501110106082506050c03030a020c010f0908190c0b0a1112 66
    0x19040e8403e52003480051540303403440d2501c2c001e0100b1850704a55100c030715800080c44401618004604407000b08031800c0d60001940410b006003c1608640c0c00e21000c0da00c0448541480320090095420580d428500a2403183c501800100c4025061064942200034000494011070480100d24680740e0400001d020503403080f12010080501210349105800c001118030000c1d0744080b04071100c0001800040c40010301b054601c000700c01019150702c2c0710b00e584a0100c1078944464080c0c0040700c5030f43e02d03100e40f103a180c0c5c10828202464880c585c0d0411242404104940f0b54025144e000c0d58001c0c6040c100302c0512900340e50042c0102c4d00708501510503038020011850000c50101c420401502400201542e038100a031100e00500f01a00e505800a000080e42c04005a003c6c0140c7e1030408008036407400e05c61600421500b0203441030700c02050000311b400d101842805000600a081d103041c03100c410380da8845080110018004085091704e0700b90701d0040154250a94007204103c0768881b00c241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 636360935 1250 636359685 636359687
    0x40e04140a1104060512150601020f010c0201020405090105040b0d031422031103060717040201090302100e1c03080f040f12050304051b09150102071814010807030f062a 74
    0x141980ba0701510503400d2800c00310391814410000c444100317121009024201120301010b00407a8000c00c82411403042c1c0e40b008000c003e090140c0784502600d40c0005035140c0c00c080c1803101c48501604200d00a03800c10202c8005038450b50568000140c00d85004002910500e40742101c0b4400c2c0480f008034000f40a1094014042214810044911a050303a080300e070340c1c2401f4180c43c2c600803138031080404c2080702684220740601c484950b1040c41490103c0c58140c0301d030b0001d0305005c1203004080c0010414010f0360200c0c200403040280e2804c0b80540a81e152076030340d0340108000c02c001c18007102c0144042c08102040504994501081e83c405030300306440c0c00341c2e0340051040e0411501901c3d81d200e00311800310b01c010100b581070041c000c0a040c070022652907000c2310b4951343c0c40c19409411403041d0500001e11803000107140440201c03814021031242d0240703020700750900c01a00003214981080f41d0800018031846104101240c1c0544003188050003020b500c900c40d6500c60040c0004001440e50407011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 636362185 1250 636360935 636360953
    0x70b12060907080906070323010e0a060f081f06030f0b161803030f1404090b03010b060f0703110c033702060f22060302120f0606040e04140a 62
    0x154a00340c840ca00241e8414104a450f0300d401e64580f904e0f5000744c00890400e034800c1d0000c3d400a012400d134407244550141d02054010400d80c400394422200c00305004a462441c090100140301d07100780d18460700d0038400000e0300c2d4021040d44980500c000c0c0907070716401ca0143c01040003190060301b02c80e804155810150b030103050403103414101c0c20556098424240c01a007030101c9120403490b40242d05405c1d540c1c16580b51448a41020030702c684419011060f40388040208040d15114002080d51010841810b0969200178111407198206100c0d4140c6021030400352000d10342c25281810f07084100c0602c4c01d003000c014441003a0540101040010064520b02030b080300408240102d0030005044c000d441a103a40c440d000950050382000bc0c400901d01e11800b91000101c0c0c049030f01454030000c92889005c00c055809040440c0c1c01042108c01c22080e5018546d10840d0f030480030943d0300d45400002d66921650080d032542d0b1110401250510a5184242480ca0100c008132180351946013030420039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 636363435 1250 636362185 636362191
    0x3090f0c01082a0c010e15010311090403020c0904061a010302044415150f0906010909140702070b250f06020a03060f050103020f09040903020a080703050307030606091412070b12 78
    0x803881031000987c0e05280400c2007504aa4112604001c0c000c000c0702008007221019200390304510401300000fa540e59000030650045101e0640000c1c0d004070f0190818060b090b042c0344038141071043c4010080080300301c951503441c06d040c030000b001850414214001c00202d82500c403d1002d0f541045000c0304d04001855002c80d80450100222035030703a0414146502c1c0507580207604281c2284a00c0707006e0401285041e00040141021803d090319806014212000101029030303501900007407100080e01400f002001c2c00520040e1403400840c082401c0f107032640b031a80e000074442030242003003c0c424262941c0b480707154071000540d500d031141c031401000b43c051800307140840f03039414600046941c0603108403110021096503080c01c003052401000010402c20f40c0940c06d40c0520301c45100050340d40310081580d103100391600350701d0382856070000741181c0681e007140703003070200c007032000c1c000d04801c074130025501e0108903158040e51180c002a40c1c2050b01c02c2e4413070360200802003164074640c4000404648 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 636364685 1250 636363435 636363461
    0xc0b0d0605040506100c020d060e012307052818090203060a0806100302091b0f1209010603081204030e0306091f050705040524070803090f0c01082a0c01 67
    0x1058564030100b001d00a070040c011004143c0c030b41c0c0c246c1c005080140079210880d0080c1e20010f5090401803209081d10344c1a10901d580c1c0346110703002c0c03061000c40c80311315801c0500f500d015808e04400c4091200204210f032646000c00301d582d0100400f541c030070302c4650b46014260010040700c6945a8840b0003035002668224482d00b0181d0000c1450040052820b1055850305c010401d030a19540070b0005142018000c00040d43e12403d1b940c0c000c020b0f10008000305185c08082641d50381000f184140a02409401e20500d0703418050100701007881003040d01c40301d01402c0c540c1e0b4080d440354a000c0c6c4640c0300184416406000780c1c0f08202c0c2218000c141c8090182c1d81560b8a0740b040b100c0203242049410890710040070500500003488107080c2402a204c888106842d0207102071300000d44941d290300312000c1200c00f10000000c201640005002c010210300d40c5000511008204030000781000c00001e0640e0750345021184044623101981c20306c145280e44c010b260075900e592151501d4003902c884500d5070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 636365935 1250 636364685 636364691
    0x1203010b1219062403052203020703061418030408030702010e030f0706110d02120414010512040b01091103061320041e050114040312260105030705060a0206130c0b0d060504 76
    0x11381c2c1c00e0081c01264400e03108243c2402c12001081400b2040c0c45880711b045d02140720320400400050700c40e20608600000c1c11590b005186040043d20600c196030350080d60142e0800e00c030411841c1e0000080c2ea2000ea0309007840b02201c104a0042490314100201c0f200c410b200b40c0307500003201c50300403d40da21040f080c1307420740b0002944503405aa03150844500099101010441040342e4100c01480d601caa050524181e450108400c41c101e00d0201d051703800f5240c00c840c2400401a008480c0b007624100038a800c0141d05503e040c400003035000c2151088160482d40b2044044e5140c0300044d184e002103860348101507111382c1c8840c031561030320306101c100354180c20000402051560080c40005001079408005614060440d0b495011078824105507609200c0d104210515911184a0500c00503580801c58403042d03250004140c03801c1290307801980600c40030402c1e03240040c5d02290491b48881d4040400004800c20300d0203420203807041c1e0050041500200f103c0d020701e41d2036004102150000c035418 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 636367185 1250 636365935 636365999
    0x90402041e05070305241203040e0a390e061905070c060e0a0b0d0b04020c01020a03060b0a092303010203040f0314090a15110708010603051203010b121906 68
    0x50001b0003040302d1004d0a114850340c0b14101d81c60301001000c90400e14505403400c241d5100101007425201f40c4890451a884181c0e000c004458038104907034036076041224081001c2c80e40220703c0c2d40800c82c410130b020052060001445a21b4071802c64005801c1e2444260182e02001c00040c0960000841258444800c1600180c403610446a500784c1c504001d003a4500b05251113040390b0281d0107060021004c5e1f0302c5484040403540d031480038040c01c504020003d66a00c0060720000c044500313581202d02450782c14030480f0a001d5010303815a0035100903c0e40e4140f0040b0401a119a030981c00038250703415130002041104008070801103110140c842c1c2c5586117001000500d40c01140142202035070001c4201e40c0c00c000625604040b844000050304001e03039400d0064121b9404d041c1740d034100a8040c0c0d10b5031010000c000b0100003000e103400320a5129400d40d41007004102c004c2c401d60350700081c1c0c00703003007030203e040202079411048650036041e904001c0e142c2c0d9031a02c10880b03c490001a841c2038600304007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 636368435 1250 636367185 636367201
    0xf0a09051c090b0c030415030e01090b07080a06060e06180307060e030d090501080a052208031005030606060706020a05130f06030b0108100510050c0601030b0108160311090402041e05070305 83
    0x20390340f0302001300c40658200307400c1c203026180c104c811901d002d040680f116011181c83c4030070300c24219614010052111245030403031025101540c003800d0420b10720314188003001004e510440381c400d0740c101103030030300d54420101d510f002c440055881d003581c2c03501a04a0000e4010781080410790076041c00d82c1524082484003c040c2c2e04000184505404513034000001454040c2c20307400b05501000f080f480010b40326140036003036a040c0b9031450488441d04000288034121401124050040030200c000300181c1c500300d40403890034010000c0041142d40c000c540784a61034007807801c0da0040c05100c020700568990301d803a03d001c003a200c0c0c071496002c20b20300014a1100c0d4880e2403114402d520401c50950094504004e220420801401c914100141884407209050090001d10700031802a040c050807541400c940c0350421030801c01109054005200410000b0001c80600d40500d42c01c64050340d29545070300210f4060040c0c884001c414402c0380c1044800d00e03156511031800390340c07143d9040009030742c0e0b104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 636369685 1250 636368435 636368437
    0x31101232a060402150f19200d05030a020c1b09091b12070e150f0a05010e0d060e010c262802040306020a030f110306030717011404031d01080106080f0a09051c090b 72
    0x4038aa03043d008681c0713200d449c0340507d00039174200d111881c00502d045500e0514500704070074103074110601404041012114503040a1264001c40f414000c1d040d905102082026440030341b04801d4014000c61003c586240c10901a03000142001081c003501b52400394440d04c0d141030484012445001c02800302250b03424608604030585a040c1c4551000290080c00c0103c40803040030122541610740404024510080c040c040303025155403515429100d03928001c0060114100e41c099804590b942009075000004d50100a0401210b00741d02e907070054100403002038429600042c01407800000d45c83c5072183d00d94022000c83c048003100b00091aa174011440f410310055822681c1a030000c0d03814000000c8101e4480100d15054000069101510b041d240003030404450607408075a81010303501c0c10105c140c410910056003460912010360421101400902000d000300141019420016a500c5100e80c0040320403a0020115800b07282d1600520a403d82d140207004005a04100c0c0003c848030908 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 636370935 1250 636369685 636369737
    0x1a0a0314100203011815033e0d0209090118030903230d110c04051509070305040b130f020a03150f090c031101232a060402150f19 57
    0x1340c03085e05540d0707079401c900f000c0c04800200100d4031410541c0000002d24200990302c940301d81040c3c6180c0c083c421060307a04144004071000c0c41c000b00000c0c01008544e41c4113404141d00d98121007050164480c0c070000e50041c011241518260910001c0c5081030507040b040100440c0c0c81511441c003070300a01010040020324118800c05182d0040c2d0300300c042e460241d1004110b40d050301c001c0300c003c1402500000c2c00d80d4000e4503000584201203501c1400303818403540c1668400c042d03041c1844542000e41d070303a010000009104072282c20295100d00100219908003410042d00107026840f0350b0f8882c20101d0010b001240c0769480c031361800323501800180590048052054001c00801110344c07454907600d043c0c44d00718481e641040601140c4414880c0590b051149290039401c20036241c0c550489030b9000030088010f148100c4070b40c1080200c81c01000141a54000c0c0d0640d00100e0003440780113114400d01a450507400b40c4000410907084442c0d076140b0029540a2581d2540c0090060894412a5000308 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 636372185 1250 636370935 636370949
    0x1090c0804080c0309030604060c030506090c16020a0503010c17013201110f031818040f06020d0e0604051c170402060d091505010801021c1a0a031410020301 69
    0x40e000a010505440290221a4001054030300d80051080024241542110f044600c0c0e540c41380740420047d0b0500c0b80c0d9038408001d54081c541c03400d100a030f00d481d0f40640f40c141c0044807188104c0c8021074642c40c02250040c003014000380841e00082c01d01400e022140c445501d001c021103000001c04054104a40c000d2004c0d00ea2401d400c3da0210ac03000300b1504401480505100e1884182c0c1e0500300200401084138040c00050354075100314143c0020307005400c40d09a40309803420b40c010024440d40c0c03013000f0b811a80c80041070028241e145030542c0a401a00d840251451030101c03a110104404501c03284900d100320f068640021131440d100540e1645111300c140068408031410300150703d5011104e070420700003042c050410310402c00000c252034a5078412150507000c8100910f40d16001d00556003d840108025030070401d000686917050a903a0940000885e2104a03200d60013980d9818400286005000c04100c0781d1241455101d01c00188141c1c03d0520038103c140c103501e0143d200f035038141d03018 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 636373435 1250 636372185 636372197
    0x1506030e010f1e1a1207060f08070f050d090803010b04060905120d0c150f061401030c0806010c14030f0715020304110d0206121501031109060403080f0403060609021201090c 76
    0x1d564040041c1a80c86130440c29412003550399885907a1220204030702c2001c2130085c403071035040100080012582d4000c0300d0038813401805006a85803c00149070001c01c052406540319000d101c6000c3c00380004440150075408008004a1170108500040c000e44655886144045542d50244031f080c1c1c64122034104150407030303442c00840520450640c0b001302c1c0200a400111845c400b00003048508502c4400c81c1c5a0f511401001211200c04402158070000d01f4100070502c00707503001070015a40140790270304001d1180780c0d4104000d42001040081d42c00e1500310b98807445141c3c801c00c0158010517040eaa41c0c8000d0440100396201402101c0c41241d103c480030090308a55820f000002090901c22640107105104440300600041d10b05445000070022500030a003a04002504442010000648464080281c0d000c82d44402007100e080341c0c2c0c000701c01b90303545e6400c0d074600300c440c041c0c0d0700002e1400d800e01c580002c0f80e4107960090300c68007407800441811641d076034450a046070000d01c01c0c4030101d81 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 636374685 1250 636373435 636373481
    0xf180103060b210a110616031101090606080d0324050918060411010801380708040e04230d1d1012050f090a151506030e010f 55
    0xa100d8210060b0000043c0c03a00b81d0240381c4005000700c0002c03104451005500c4503400f4002c1c454480c01c49000c6000903142245081c115152510303d890f0600b0026084c400d65494407414040c09500014010b904620b040007041d445080d01a00c40d02e11030030078000a070034003100300704000d0350300500c8040740210125500c107a40b0f000c0c244240b1000040884a05010000d82c1003c080310a10940340702c0e612550500540d03035483d80000d408458183c02902c0c1d844110306000074a03281c45450340c1c00c03032a0040703420050800360001c0c038a03003481110b80c0103110134030101c2c0008202019540642c040d13442051580500b0201001c0c1114034100e0304000800c030b03801079010446640c01000317149145a03812106801c141ca101c80802c10b0090400c4c004000140b40d4480945402a244030703032900440040c1c0c000e00f95040488807240d072900d032074501414110011500f0844100740f030744903000c290b080315010350320a039803104041c005081643d080d1002c3d50a100224042c811035110b00345289110408000c40c0b00c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 636375935 1250 636374685 636374693
    0x10203010f090b010507060603260f07030c050c060a08150d03091503200a27050907091e090c02070302100c081e070219030c0b030702031e090f180103 66
    0x91401c000c0b0313040c02010000180459034030300a200140d402091304071200c068800e102c0e031401d13a900d0400006804188107017106010405c0031180c02039010303c0d2441c880750f4a41000da08103a818030310507a0080700000e4030400e068000c07400c1c1d845005506549010f402d9001d0a002d48081c84440060001d4800001807000c4042101c080500c203280b480c0c00511000041c104001e210711101c40e00300105404906031686960101548011000c0560342b06030207144490380c211003403458042e040c4203104220001d0803c074440c4855030700a08960500030b1440c0668107141480302c26070300070025100d0408030b1114071280005000303400c9a50141c00d03400c10b030140102c103c500c00c041407412a6496810030019050b03c0515000717928a0181c080312503030300c04440c4104401e840f00b0130011105200644420404240b001422200b05e0b10443c3c1110ba90750b88141c0101d09500c16010342a80b0b4441a801400407502643c014110105081c1d811500200010041002c2210030749440719221804000600c002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 636377185 1250 636375935 636375941
    0x50102060f1503100515010c0803040206090d0501020d0b010e09101e0302060c1b0a06080708071101150906080304121e0c0b180618041d0a080c0106050102010203010f09 74
    0x101400a102c01d0400d000b803030010303090540004d12480115118014024028441d5a03e8020744000342840400a0500c1d41e80c50f155000080010b03100d0709010800342c08076150008584021a8000d00841d07544000c10340300c90003009a408140e00103001c8400c501158248054401c1c080c80b51080c6940103680b41c001c1a56401c02c00c2c942a03032881490700320000050321481d020b4801108500050aa140f00300a04c081c0e07401c81d8041000d00c47c00b01c44004001d200c2d00101d500390482c90500c0e1022540d80c0b40e820903600b65000700f0891542d50301c2d00d511340b64090381e4002211305076010805c040c000c2580cac881c9550390b2802680030390352900c040079110700000b548680180c0c3c6e181500fa1501c1c0022580d54584080c1c4607510f5208100b41200020038142c3e546402d8465460094200c0303c6034104039000f00b03084141ca00b10078500d4007a540e143e00700e0b04403202d0500781c511601260001c840180450b4a0710240c03070b401c42c4800300b92660034410701160540c010300039039040e20001080039001a10303009982d000303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 636378435 1250 636377185 636377191
    0x10509040e030904020408100f060303050403030807050403240b0a1a0306150316020f1f05060409060c2604112101050429010315020a050408060411010f09050102060f 73
    0x109110070440c403103d82c3c503070340090001822542c0140c52414844d2040c5030039145903903081d400c07482c500b090a00000780c10006407000e4a8041c580070a450f518411305440c42d209a0700094440c40c02d2450032440401662a81016501402c50a0041704807007418044180b015004018a400310f900640450300701001c0070319884840145a41801580c801c0345c10702e03552090b01d111042c010301181c05001c03d60108800c01c16040942c000340b107085d501d14460581b04402c0900001c1064030340c400300310a91390355044508100d40285042003011196000500340c094248641c213038070541c409401d007400740c0c0b1040440c030480e0000c1030840360095500c100100034620054201820310b40030483c483d02502485443d12a5204294400c000d11300c0120038186840744e541c02d007111131105c00040c00060440e4240007410340c1da964015842e5010b10b00181c40c44d0003541c114002500c5900d0401c8103002800c0c40904003001d081e01c1e008044c1103215001c0f604240c10340551405684800003040c4081e5885004682c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 636379685 1250 636378435 636378461
    0x20c0909190501180614011d0601141c020913020301150302250f0b0a0c0e060d0b1e09010b0717090f0603090a050c0109120f0204110304290601050904 66
    0x91601c1002244d11207419400c0040c0da0003075031221264221400b901180e405000500c000070032003280b410043c0e00140008050034100140f912011000402c110151040300d8030b201c0c3d03175151480c42101c003c8000d412410545101d0316058809a010307103c24401c49050300e80f490507101d02c000c51702006401a40c80030800f48005c5110325420707081411034500c0748942c0d80c03240c400398088050509240c40e0200000d00420019807819681c20b0403590003000d00c86060505469180c0c5135081e140c1e4542c0207200c14001160001458002261a41421001e0491800d4121b0304014140d803582440c4915002d00c0360018544001c0c65543e5981e08105809080384050080442000300059000304506400c00d5a034048554041e001e0201002014800d0405001081c07070241c4086180901d002900081c2280142c00820000b42950a6407501e40100c0c0d03622500a08003035407070400e460031400d22500030702410101d03a80318041c0710541c401c1d580018040d01c41651101d0800d41c40d4401c0100910320151006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 636380935 1250 636379685 636379691
    0xc0b3f16090302150405130513121119060c0c020a1206090c0305060603010e060603191104020f040905010503062512180308100e0403050a0c0204020f0307020c0909190501 75
    0x2c0140d40d080c403506080e201031060a500c5901e000c080c050b41c00b0100781c41c011400d081c0820811000d07074032031400030000d0308400c0d00380c0d007078a4012050b10034844010881e0250301030620b280300302208982181c030079603118850400200c0340c411030488180b061401e00a6100711490800c0203250800c00d003001c0c10383d00403900050410788a50301c001e200c44840c0d100f04c0d03054120a04200903440e0a05c40c07000003000c1400544032910f00100001e4540006034500d075032811884c80008180710394207010b04040d00c0d025000b15a50403440094083c6a0060f10401500d01d0414001145c0344c02d0100f5454002c0d002c5402c02c04c0100c182441503a4040d03891540d1350b0400c45a1910a15055440d00401e01c080065280300c1c0040401d60070000d00000000707048030080e075000007041000c84400c21a440d230050301403800d140c5601c1e87c24001c4400d00d80f0320101075409400400c02c0380c0c010400d04010340c0148810740886030142030078000e0101e00b41048444581c29040f82c110400c20f034810300009415148250000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 636382185 1250 636380935 636380939
    0x307030b0a0603090303050f010f0b0d0204050a08030304050708010e06160e0a090614031c110703120302040f050f030d11011401080105090c1806010c0c0b3f1609 71
    0x82494030700964840c40000b501e03401d841c005d141c5c00d4410640c0284070b03c208542d00d51f040c40c0910707000000c4e0303115210504000141221070000c81d40e040d02c003d0f19008040b034003ca079503010310583d00d80003610240e41c07601440800044a4030140f152546211114001c1e003c81d0f920700000842140000f5151030031f21590340461903481c1e4919a0b81e1003d0000820002900d03070a10700d0004081c0d1311541c040c3d000380e008444007000007502c080c030001409107500d40007041c14040e440c840e0a10000d41d0000303104165000071011040d800d5000750082d0340c04845848061691041040952a1040301c400d0309030b04030b92407100301c2502ca64003000c0e807114040d00115281000302804480c8880903480b10700030340d40d14800e000c0100d90900c9270041912088507c0c00e50f0114406088890b20005000309043c006c507042103408004080c02d0b40310042c41541c00340d9844000c5e1100c500ba10401808105c00111402c0003081e010701050b0102c0c030700345000c0300b0280d003c541c0c03501c16070449107407903803802001d1241003400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 636383435 1250 636382185 636382189
    0xf01060c02041b090f1a070204050606160b070216050609040f150605090f01140d230420030303280603020613080606040902100e28030b06060c0607050307030b 70
    0x3e03003001d210841e600c1c52041c43c03518003403a1665255420201100c0383c0c2e4159440c600d03125605840c00283c0480e00060700d6101c10000500c2840f590310441069020240301c481400521b280e80362040140e13800382c5046800981000741c614205000e40e0703500ca0014440e4400601f059070140ca40924800700000750a18100700414142c05198003c000007100082d4441c80c80c2090503000c40c0204d000c2c20486e0700b1504040d004001070084080c0c1c40055965002130081340c1580001c2e4040040541d0307102d44042c10581401c1c405211001c0360004c0c001a41c0b1003080b25403c00208036441009942d040310303040c1900102540040060031070f490206511600e012025980f030303000030703d825000d000c1003002d00c0b4a46401c0a0074044000c0049100314075180c0c051b005038981c024924188415490007404000e104000912a003e0400d08200b10b10401c8000c846111304c4e2402c01401e60b0300079080d80050b40d035280200250b41c45610381c2d24000b5000900800c4e5454003c202854005403942000301d220104640 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 636384685 1250 636383435 636383471
    0x3030e25080111030106050a0f0c06020310080f0706530c0406020c090703020d0f0209031207050709051915053c130218090702060f01060c0204 63
    0x80d21032541000d0020030440000300744503003583c40280744121800c0d580741c0303000a015400740403001800c0c4003044042c8610a4414104540c0c090f500540c1191281030144210300000c242c3e00480815114424030316040110000c0c008044441660f0341e03100b40d4940b8600117401c80050400782e02740c0e4004000d03803000d140c8818003000035250300c1c006402089020014000200078041c08a0709843e204102c140801e40c0d01085c10154090241d4542204da120210110300034460b0090303451180c0e145c26001340510b9016002040098000c5040311405910000e001d00140b054400003000365000318010040404e00360021580f0102c0494200b16000c582c180240588100342000e800504500c90706010601d41150700140380402c4212210070801e0045042511400e100c3e8095402001c01c198055213a030744d6800c0000c202a8080103644564400030007000041724200c14510a4042c94001421a03100041c0a4840c604603003a20601d64a00b81003074071000c02071841a600240c4810030b0b80000c030300740d41c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 636385935 1250 636384685 636384733
    0x30d050402040b1e040203250c1514060d11030f060a113a0e011406040b090c1608031f051009090209060705060705180a0e0403030e 58
    0x145012645181620411003114001010203115480c0c6003100050304840001807035401c1001d640040c0d403a00d946c958042034005141c0b4900d0307007002461900b00401e80c00313080b58107800d11803078440c034922440b00703001800c2e10005c0542d0500b00c0030084c0014440e15015a82e120058060a807031412070503500d0120b4144041181c03a80120340c442010f00c4040d2002d4820105813602e1504000c3c1084884048003071291a054031041080b0400007001d00d040261404402c0d40d580e0880781001a51150744406000e07003c40d03c8010b02e801640800583d503824603028070500318400900d02129551403003505003081e0098118038841580301602c0c40d000a103103000841c00b80801514484511803181d07206c4800d80201e0b0090f0340184201011708148540000b0520240c86650030050b80341c80c1ca40c0c0124509004e00d40340980188981018003c0c41d03a00300d0700520650211100b1590070b001400e080c043e9000442c0b05140304504c604000601091190b44540f003440f0710703013081e0781d080491031034214207000d920 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 636387185 1250 636385935 636385957
    0x120a050717070f140c100309050115151b11011d04110c060a0b090105010e1201230c04063c031a040b031c0c15050103020f0103021c150803 61
    0x240300386800f402280d0b50001102c130a6080145503035034066011404040f48565403a05041d2501004820802d00f0340201c03101c50b4410030b45680c0d9a59464400c4006400d840603100031a4104403e001107510380f038003480d041508001f900c1a02c1d911400110340c1000c0c40c502d023410f041842c40304240c966031031b40a041032140780982065158004220703898140980075152500e5545480040096500c407012550b045038402d0a11840010708007001c6070017107614507421000c3e0351078021920503003030b01981c50358441ea00203030803c3d07207030f81d102443c0c10401d02c540d004140200b01c1401241c0031441e0014600050380020603800001c0580032056000e49141008000022a40340d084001d880c402c610084a55950204c5040c8400303c80c0e02d002c06d4450300700e40440f0000b44c844640c01140e2601548030442040c0d440716154800c85000c85980000300380a00040740b00d0198080c80c11099886070095420710302d008080d001418078581c0c4d0100c000c0814810202d5410300303030320b0b0004113a0414405402d5001203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 636388435 1250 636387185 636387203
    0x608071803030207150305040b04021302041e1e030f060507050d140a1104030b0412021203090c01090905010b090d11130203010f05030a050304150c02040c20120a05071707 75
    0x341407219404020717441c0400c040621b0702c010040070070150304c801500650180c6640b41c0503000c1e40c0410707010b4816a000f949002031805140b40381c96118000c640203d42001c0412501680c0c1040c0d404030103281380c40040c11000c448541c0320007041160b40119040903039820b20742e2510546076002c0007030710300001800500e022601e0030000683c03c0f501a00c40c0d00e60044682a141c103055a450944281300600b003e00801ca2a80d403612030203008000c0c211344540c4200da6242c0302d103410f055807640c030058600003600145a412000a18965034000e0034107980102d00d4560510000400f444070464001340140da24900341440c1d280ba54503960008441d010040c003026949605160b2003010482c0300e82d001501035404144104041203020040d00c0980c0c1c1401c09281802140741c000b1614009240000ba620ad0310b000100c0461942080754801100724420704007658406807002503458080d1032540c014200802c00620318a0744c81400201a1701e131140403a4002c0c9a01c8003903a000d0b58003c60303412100c09007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 636389685 1250 636388435 636388439
    0x180415200c0d05030702031204020303120f0117030702101d04061403061f15031b030603052a120a050d021f060f030f05012003071b0b010608071803030207 68
    0x2080c0141c02d0a40001d0810034554104010700035a80d10132006d04a42c80071a0320042400c41d40d0920840700c066400351907a040c076050007520040440d00c203118441141c602da000005003074030003006655509400802102200e43c40a00c00d850001802466025004181600c00400d03500c030320562020b4400d0007500c0b0b1540364000d040c145422030250580c01c0710f035a40365420300c0601d401d01c1403506131151058a01c3e10320100404c2603000d440d0401d0440ca0456070701c02008219075241e0302c2501141c4c080e90883e001d4400383c9040c540d481c02040244601c6901c50040030040d4149034400f0008800c041080359050082a2501c8d400c0c0071b4140301020044e0020090034a140c10f0301021113840d120450800c0142c10314000e412b14092101d840000c2032007681141c40340601c003003035009007a02c558000c0c000c1d03510126414503c0140c2d104035154004a01106120301010b03015050401103964820003044680c0d092000590303241e080181000c04115040506c02e40e801e409003ca1802140300c0d13002440d800d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 636390935 1250 636389685 636389707
    0xc1e0e03070501022a0102030d0615080109200f0f0c0714030d050405010e0f06071a09030711090a0e1f05071103070f080f040f1418041520 61
    0x18480d5116030f045601154941201d1010403400700e4001081d41c1c0f80301c4111a1010042c0e085015014042c4509131400034000780d00b10750035501d00e510710b41e142d8800321140c0e2110400c104940c0f00008460b00030f4a01010036586450b800c00500d01864071712007540c1070000b21075040840783d20054a04000b0b40103520108115882044400c40e0300300c084000c0d04a80610300c400412500407446000d0410402e561620f045881d17924a05048a1340507050f5551954141044001404080d15804100054a002070a185404801d888800d580014040412613801c0100301d42107101400c03000c0400ea0712100905084010043c1459600d560403981c40d03185d06d01c0d0701c004110ba1004103401c040c4121a940c107851800d010084409460340989001d160398445c0c01c00c262140512050038190322030000f000b00b445010104500d08032500b0b5090012465180c2c01840050007501140e5180c581c83c0031b0105d40024900c461002d0102c80320b80c3c00117040c542d400c241240003201c080c00740c141d405001030b400300e1803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 636392185 1250 636390935 636390943
    0x903070209060a1a040515161113060b0901020c0a05060a0e0a05040c0909050a09030f260108030d0f0c0203030106050d0b0310020c100b01020601180e06010b0c0d031401090c1e0e03 79
    0x1d00140031449040c1040c000c052096203088c00c50040103d00051010302040d9079002143d440c0c0b0342d0310385003004059181d031079142c210ba020110541c00b500c2035141c1d0f80094544403040c001942c401400440c00c110144400ba10f10501525070568031100e2070001240507101c80c86030b59217441c055075a060280740f0702515003007103920260030484510b003032440d10b1021070740200d4031010ba61840d140c40800c82181942900c441c11040d801d0344100c20b6030400004500100101600c200c4100400801c035080074100e400c0122500c000d007500242c0c106200400c680c41c00340000d041403541140c0702140400e010400241071060180031f10021650209141717401c40c10400c840c070803050710304100700543e11094001030b42c1c40c3d00504c6040f4214840d8880d0880c2d01d4199088110542c2031031085903aa035855004d4a05c60350441d0b802500d03548a14865800907902c03e0040c41180320b0030140e9a00240d00380910340000d441803d840b00c09229488141800c6400c00341204c0070104000e81c1c905580c001007400305424 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 636393435 1250 636392185 636392209
    0xf030a110106120516140607120c0204141905100515160503042c01030206030a0209090f040201020f030f040603090c050310050a0f1413030c0515090d080903070209060a1a0405 77
    0x20b4030803038106562079031104000c48110755040080103955030322715102101c8640d00008000d4105040c03904650402542181c00c1c0e020b88840141030480f01c91034400d07802200d904603400141045455020440f40c03e00c51804c55001d59102d442502d00f00c2181001c201c8416a608211101d84c030014081188582100c490400701d4100e11000103162404002000d0908040c04080c2c80303080c0001c08900c00c00e00540c125002c07802d0190000e03203286043e41c000c550140c4e040b03034141e01500561900a5440c04c6c04411110650b0010002c03608090428504400800103000e013101c07454466480440d9550307041140e062000f200d40008541454411500707000c0e10002c16612008038144100780140d4030210288990200110354121000004c0b42002c0300c00c41c1c2440b02c09019401904c40060300c0300a0200d04900c1040c1150403100c6030048404100c0e007030307030045900e266250010b011100051070001255038010320010080103003140c50381c000c18800b59142010058400d0000740420480c00c0120308802 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 636394685 1250 636393435 636393449
    0x50c0d09030503030a1e090c140f0108041202100501090209010e010906020c0d081207020a03020c030606060301060804050f010c0201060504050108070e16050f030403050414030f030a110106120516 86
    0xa1091a6644056981c00040c12101849440f000c4030828244200ca80e81264009401b09001c6002c5034144036800403002c0c01000d0741251200302201503800c2204003500700d140103079107c40c001d0fa503a40b20500c5002c14200e2a4046000e0314038140c0c0048605d00407d0f019110364140140e8440044c00058800c110903422981404226070301000038580100300810b007020103641400c0b0300c41c0d40303103007130310591040300d07410b099100700d071024003282d150700041c1491058403135000c454501e110003040694503482140c103198003800400040c000d1600c10740300d00760010710800868418030060700b541c0c3c0c05d4032844058800141e640342010400d52500703004280c01450f800c40908401030405202100d07400005204289003440002d017a4411481a01264451400360429075120b00781454000d29a501900c115003d21150030b04140301480c010410000f0f2401c2e00008500c1d21441d48415036084100550915481d541c0b1000021440708405260f90258411006006a00041440040400c810350400d031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 636395935 1250 636394685 636394697
    0x60e18010b040b070512030a060e01120209010302280e10060e0a1a0f0a030b270402090a0e1203090d1e050922050921030f04030507020a06050c0d 64
    0x7030780000c12142528003403c0d400766201c1150600a00c1c1103034080d070300c2011070000001c202c0588100e501c00d6041c2d03805448814000d99035007026881c609100380340a940850b803240104018900307101203404689146544004d11000300d80d5640d00901c0701d0b445000142c04401c20041140714003e900d50240c007080c10080070302490381e4080b51a01e015801142c20701702a10421a0008080780142c0e14000200c0c8801365890b101014014080c001c024000c80c050005280390080c0c0c200e8002c400d005400a8119541d130b40d0355590200480801c3c09451103105503a200c44a2408950a01803013460401060302140c0c0c03400c200105910345014401002c0401c4079131030522000b84d11442e00c102c00302580d0714003242c45900e205d000546010380004101203044c141001020604156000340748a0b250980c00d8444450383c1c0350345c2c0d0a108a19000840d10150304100160010981440c15a0454064601182001c41c90350104005580540058021500105170114825010418000c0c01001c0f4a030039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 636397185 1250 636395935 636395939
    0x20a0c0302250317071407140d03020a02090c0c07030b2401020703150b04050a090b16170c070602070f06060506070b0c090102100f0b0117010807170f07060e1801 71
    0x80503402010340801001c2c1c8194130020701c0600b002d41c05440800e9042011048018400501c03a9504c503118071401492505154904482d850400030840d40150142c001d041c0341410ba600308406584000d00f803540410081c040308811090800284015501c10600c403030003420562010050302000c0d280701c100d01e4059021840703150341c2c04160442203e900c0020244500b502d59072190160284600c000e401519180402032101059006288c42a00607281c1c08130783d0716900300705442d810b00301e43c025000c1203580b040810100e655400703040d8443c442ca620181442d0140c0c0d10070041ea0700041056030441d2154080006000d814420320b0000c0000310340903450308405603a450300d15540200510f190b220301103400c0d50180d0003031001303c0030455617200802148100e00701c4100200310304008140040c030690b51400380c0008014685068946040c02007104510344020b4400c440200d8107106c00b1f82c00790b00101020900204150b00150905803209204201034009208842d4000c40c0b031560b2042000f001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 636398435 1250 636397185 636397243
    0xc0309060506062803091a01031a0610050d110a2c0f01050315151801020705211203010f030b1e040201080c04030506180d111506040906020a0c0302 65
    0x1101d600c00c5924101340580f07076810384240c0c002c1c6444680603003660750b6403108918008074441041d040e1b03885408255504a0b201c100c0b0185c2000c100c80554001001041801000d030280004c3c2070074016081d00421303a49100304420341f00e50054501100410040d403589500250030349c0c1c2c5a40e0004c00096402c2c125a21240020096007512990a060000020110700029520395620600340400303402005c245940706101c80e0b03564403101d410f4004040400c6140213661000c180702c0c0031514002d0006070f540002d0810f002840d00c00c2452810f00c1d110300b840c05542410000040c5009050b810080c403a040e01d5818280f072088401010b24503810346192000b2104401c45010640142e02860324680c036607100b0140c3c0700140f1403900050840d20540003041004280080d81c1e200c100307440410781d00c01d410300b92000e41c0e2109450416542c26005030300030302c4001104002880c0c0c4100b0082002c500c000050306c0d0702c0c04036400703e01d4940c0024024a61034040c503170104603060303680c0d2110704046c90020800d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 636399685 1250 636398435 636398467
    0x24050312030103031815020609060a0c020303010e0c0909040c0302090112150f0612230f0303070f1209050a0b060613060e040f02040e010602070e010b04060810090c030906050606 78
    0x100a050045000c2080d5142e8204100c1704060700c24072507000c42503810920003a544602c101c07425040c52141d0000a40c40b11024011200040ca40380c00844c1941d007807956844210000a02d00550030006022045640d42c403440100d018a01407600c84990700c4c218018401c041c00141c10184422403408880000a00001d41804102c609000c00080c07003050017102e580076000d1070f4091402c21005211203000d0040d9540643c5403141407266180340c11002d000e40c00e4880f6140113002c851a0418000104102d0180444000744d032a00c1c41c055036500b9440301c9a20031a140058142c03070f6540402c01c1002000701d2071652903000a07045a66900709041e580c00c20606e03189a0044004024001018503040d4036a40c20102030100c0302d01080d500e450303c1e4170b016028510240310380741c0103200b144000140318142d5202a41a1400010180d00d400d06000701602c0c0c2500c06490042c04644c50103000948290f18420001d1490281d54003262290603170600c10203031080034042510400b07081210703141901c107501c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 636400935 1250 636399685 636399689
    0x50604022203050f150a0209040b03071e050301050108120d0905030a120c0309050706030221010b0a0f030b011b0201050912010c0201061e26010207231c050906040801240503120301 79
    0x40056035502c0c141009c9406040d1014907240c00d80306002d004101011005c130308204c00307001e07407502104080d652800c060a031102071260840a8001c4006041c80c0c00d10b000c010121a518510b0104181c922aa100ca00d140d02482c0040e0026513501e62512160969000d91100d0000754502401100380740d440d1300d0b44034040c900c02c0106040d03000036080c1d0b1408030398980c00c1c010f42e103407024001150b0b59100a0305465100c0800c4400086140785411001c9019200f00d0020b034406070b68284c0080c2d4625105002c10094030000d030705000040c00b030710150b541c50709840c020700c1110070008617807031203030010113404d5400540142c040b0041d4100e0ba55622070095402500b1196108405e0540000c0107281189002e4003030281300207540001350305418484020707d11940c1d100309005030042c12282a0803903480766100d010f10303500d280e1400c014075800d5201d10081c01544030018805480d00385c0d130b109850f084800b0700c001100da00644000044245001035408001000c0030350141400c10565411100c440c4414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 636402185 1250 636400935 636400951
    0x5160b030a1406211501081c0c0b0f07030905030d060302030f0706140f041212090b0711090402060f0c07150206011511120a0c2105040306050604022203050f15 70
    0x2510031840c0b071309030030050700704a046028500032007541c48410301d6407600118080310342c503403c10401e190440c6100c0c2c1c07851000d1a810125110080d01e0300810700c03080c43c1d4050f100c034041607103562920002c14400e2004100b540d408040c005007052640c4141418454100c05204590704420000c01c610758019a90303442d01011221607a54541d07540e04802143e005036000b40ca4480d0003170003000100466a0404004511142c494000c00c0d580e5008849851250354030046c022410714012450900b880c40d4255081480104000d00b0490f2088c003c0c007251300100c1d982d02156200b038034200b000c0031882c40d1841580c00c03248041c0c103c1e50306100941441e0442c240f0300204201c1042082ba42070502408147c0c4910b84401c0341e01c1e075a0b01e5507000104420741c0c412098400b108211018120f0b05a440c0f00203840d001c2a883da18100741c95074403100c6c0140b000610080c1c0046d020411080c460741c0610041d1420030202c14040500e5081d07041152404502062164a6600490513080c0c23000401b1010b42d07020400c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 636403435 1250 636402185 636402229
    0x218131d01020307120b1917010e0303040c0b0a020703170a110a020f010c051005071106070f08010501031d010c030e0f060403020606090a020d0507030e0d05040b0a0c05160b030a1406 80
    0x3d4140030a999910050b0195810040d4950208c0c02c0070079400541e01e8542068000e01500c016a04015140d110545001f4940c07016a08200484c0000c07030090301c80c1c0d101c5401580e0300c45603251901c901107041022082121040001c8440340030f900203854410051042004101c0340541d6400f1962401892080070705115401c510a01000410062038155400721002801913003464140601510b108100542d02801030b0800030780c82911030700320145902d5140c0da034038559918200064005000e4041d2507280c108000c00d00c0454414240150000d00e440707079074001020034924081030300b0040c0c4d1205c05560340d081b180902c004a9400100990450421202031909848903e6840c00902c146980d0b00b0708a4245820002d0042e0154440094000210141c3c1c2c00c000c8081022030320303840303240922041d0400611652001d180b0580302140741d5440b9004032942c000d488400c200b001c5070554010950510000204400344040e802032101688501890b85041e0030b02200003000384800800400e0095a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 636404685 1250 636403435 636403451
    0x1a0405040f0501090309050406120507031401062402010b0108132d0b06090c0a02150a0204050d151401080d030c0203090a0f0519080a060218131d0102030712 69
    0x125800d01c50640e9900c00000c1101c2002c91a000e04080d556100d1640300714034140d4005007800c03010307006442c11540030006c0c140050450366a17240d2004104258481c1c1e41d40c466012650b8003030204010685d92600c0303072988040d04054002420340e1104191a41088185024032101e00e540364120110701e5488042121310559043d01e40e819025003070501d14519100c0070b001f8052180800080380100c0c010341c2c8480c110759030342034551a10301c1101140740060703001c0e030f04544003603004001e80c83e000654008051b1a0550740c00000d07aa0741131000d0207a83c031000c03020880c941c0d0340141c0304602c10000280a048010740c0740002407a101c18003140c282d400c1c99228007981c89210320034401c480304168000c2200a42588521018100c08494051140680701a902001d50b140c036504080c4221039a075001001403041c0c5036201000b030f41110340b0038483e18143c4520701c010707551240c03005c08459191100001d0300e44803403503028000200c405003504080c0d20400c103200d100b0781e101511802200c044080030407510 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 636405935 1250 636404685 636404693
    0x303072d021302161703060307080c0102030702010c020310050711010c03060b16030e21010b04051006050a1119060b0108011a0702150c01020a09060e1c150c0207090f1a040504 77
    0x840404c0c0100b2040107800c1d90034402d141a00618005d440c1913003200c0f1181c1d121004030f039403111410307406030259105001d004010742c81480e01d9540548060142d4030b440d4411803401c025600c040c0d034244081401007101d0404460248112403031070311142b03400d1008524118400c1300d984124103070f005078200789a03103010034903010300240240c014014102c1303202c0b2640070100707428002298071040030950038400740302050b1410340079a42c040c07440c80c25520301c524078266042d030f101c0c3e01c003810b604280320600030440382d07000c02400400740c24080b019005032048200d10f82017044402caa08400d0500c10440014840e401c2c500200d000144000c2514550b80c241038000a801d011101074400b105410028105800d00381c190041c0224041d640c59040c003240c0c4501069514044000a4540080304a000030726442064050102c1e650301600410810250381c8411206454950303030104056407081c801082180c00c148150a0482c0d10480c1c00c2000548002c0c0c415200d000100c4031601c0395803200041410301c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 636407185 1250 636405935 636405967
    0x901180207020a0807090f0227120f0610060206040b0601030e0c0a0f030b220201030203100321233109050103110f060703110c0303072d021302 63
    0x303190010041005180d44d2429544c0e680c000f4000c588100e401d164600e80b40c90102c2c000d07211042e0001410001c5034041039580801e04a40c1e02409038002820b0180c0010124284505c000c11880900a0010341c6040d210505011603541e12080443d80444104008200700d0088140c020a00b440c01046041152a44d171380382204401ca11588039424406c00a90303620040750b00d208892141c8070404865844141081d000061424158031203180610b048005622903401582e10a103004801410395450751101c0c404261800300c52002a00316801034940e0325041901c06001202c010802246000541907030031050007015108800460310300318404104200d41c9109900c003820a41d4540380e10f54845100000d00002e10090700c40104981e10251300b4204000030700d134071400c040c0040d4581000c82c1e40c00c88503040900e104560502804498802542d4144001e140c5c40703000764180440c080d0b0000032181e400e06d40401d0040002040c0d08800010303203800c0c82c40200105401c40050310780600103c0420340d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 636408435 1250 636407185 636407197
    0x1f1e120c050c0d0206010f080a0812102408061905010507080724110f04140f0603270d08190e0a0312183201020f121509011802 56
    0xc60b0207600340916203c1c0e800961a0b0484401e0003e00902659415000e40c55400d00344024007032240c20065a10014200c9050030b401003400c0c0c000714801643c980044e07010213420048040010030440040050031761000d08560008800c595004400d00b80900c401c1c0f181c20741d440342034113000300801d60000340007504055988858000c000012428082540501000224085048010701c0c056004802e0070450054911201c40d03c2c2d00e2074a083d08102c6680120304041810036403001802c00030003115203034400035500038401c80c000081c0e2060250007140814095032020511540103c1c0300c00d4203258080700260308110908200101c9103c01c0d5001e40280002407202820b910400941e030080542c4105c074080300f40c03d144410046412240905812918100c4e0302a02110704081010300c41d4a1007405180064550300355000000b412130101421390304210070788130500801140c2200e0002c20114841c0c0d00401c2002407548200c26200000c50600040c00780b00303070010068807007880a4115034101d40e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 636409685 1250 636408435 636408457
    0x190503090a090b090a050c0f090301020d0e160e04020d0809030703061407030e0303090604060b0a0905040b010f0b070803131e120f030b01020c120703021f1e120c05 72
    0x1e801e8448404001a1041d035440d02c0c01400c0102c00503490038114490203002e107088800c12483d15503804800032181c0c0041c031449030700d55403c002c3d1000b010444d104042d070282804000d84105880d80c6628404aa015030150b100f25000d60104070069076544841c8101c5607000c04110b88408094022924190540e04010182860b2910111042e41103d0b000e1380300340ea0950b014401c0ca007a99102d20380300d0100340d801e00025840400801c001400310b82003220780020150054203155624a038a0051b150161410ba4080b11200c00500462080507a450050010b82004a14180495503030076110321000308002519052401500100712030340101041c1c81440e0004d0980c90400d40c10581644002e076040c880200c1c84a44030014458000e0041c50b0300494146c018100380c40e12074080c00035020014400d44014011080007000583d11000d80000102c0503260301c44100e40ea094000c6c3c81d0341a9200c0300070b00c20300300d044080d01265001c9100010b01c202440081181e600120040d281d601070f103041c0315 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 636410935 1250 636409685 636409699
    0x1f0603020c060c12040210181e1202090c130306060303050901020601090e10052509140303090a052419081308030106141905030412030e19050309 64
    0x104598960040c000c00c030301141c190307101c6480705010fa14951240c0540c090168204c0d000041c054030342040288560042030804600f64031510540704100d031516000121403003150b000d074a07241a90409a9409840c034038448074441485600051403000380140301c15602e00780020411440c1c255610103d00456001c107044c030506441c0c0c50041c0103608580c003440d006200b8003000190f940810300a00385508a850003034041943d01100a00203807000610030004009044950540c428100c0f0740d02007800300035500c130403002d42440b103240e0000c050442c01a10075030080c04550401e03501d05403900100e5000710380819103282d010070700c0e0003500c0c01e40c0c540c01d503082d402040c0780a01c15200301440e000d00800c3d41d129040707503807056074050b030515505001414510007800148145400317410030b0145040320609036800c10b0307031000d05091a0b00b50300a5941c009600841440304001d2140210000f011690074180881440151136541c1c80c0c6d03c0090b140005041d050219084c41000e00494400032400340c4a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 636412185 1250 636410935 636410939
    0x109091703040609052a030604030905060702010c1e3f120510081908030705070c0e040614010902091807031e0e15070c06090218160207050d030210051f 67
    0x40c0399071b210402000c44602241d81441c0c6100c0c5404501030340f1907941a07c07079108180c00c00003403004641000200301c1c18410001401c401191000f0084804e401020a60456150381c503d03020b1003a5582100840f146408141e200042140b558801014512054182442a03a1201d4103e800c03400b1403400b01611854201445910b0942044560942d120441141c00d4520541c8828204050040014160b032005101148886100b000180f802a0242c03001814060b111105d0a02e1018107480c11902c0175980c400116000e04440300540c01130401d00f00031420500c120001c00e459080411002000146140000c0c020b940a0f80c082d155110503450a00101c071075a1902000418803c26003860302e01c10000d0741d50a500820403024840c0000b07584a14000e203130703a540d1601400c005e50040303a2000c0c1c4081000d40c0f00750071075075891151007581c030456490843d8181c081c0c101800340d00003e00950390030310b00c0c0340440e0300040c42c2d0b0b1800300540400240d56560301098420020080c0c45850310070b201c0180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 636413435 1250 636412185 636412213
    0x607260907150c020f1e090106110c0d05061b040b0a030609060b030c0f030a0b060d0b0a08070b1c0b1008150a0e06010309031202031e010909170304060905 68
    0x550042c1c030001c02c0d8181000c2c100140c00d0710501890400254400c11039100c40190b800c0210580d03e5103600c0c4000c01c04007040040000312940c5d0240c20070320000308480d0444400503070800008896200583d090356078200180c503041d8031a00300529000c042000692203040107008081100c0003000900107258940800000082c09040e140c40b074540a075013801404100c038258441168000c014020005281150402c88201203030001041411416910041d85e00d00344c0f0341c44000e20300314079041c3c00021184607650410015640e56005203885600c9168240321488506081301c105224000c2042001d03071b23003407540754098039540c0c40e5290490420900c082c0710f241c02854850040c00101161111382c0c2c004800e102e00345416115001c03c5d040c20002080700e55000c0e500c207180f094020714140300000c4402c80410282d070303c25600c0d0300c0c440180318400c180c00001d900c035041c09040b6824051040c0c5465844008088034810640c005445c07000001c0780070400c180d4042d0002c07545c01010b45181c0c403450700d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 636414685 1250 636413435 636413443
    0x90603010501081302270a27050c03070f03050d2f0a0f0803010e0c0a1209050102220602010c03050c0406030e0f0709020a0f0e101d0a0b0301090e0f06072609 69
    0x440f005818006e001050f05072007036000f042152076880d2250f80006c00200c11541801c0d04441048d01c03c0d000301004076035551018007259020306103d030035040c030103442c51612500c0e0508403401d031030802c102044450603181c1090300d6410888206405100038140c40842e21341404d240030001020594140c080408218010300139504882503e200603840380c6d100b030911101441b945644c0000542c00154000380303d12154040c04403580a4400182840700b802c45036905600002e0540c0f415280000042000319424003c1c9400840c4030724017488941410040c04440d4041d90003000c080c103071208240052041d042010800e00d004040c111000b480d5500300c400001d500446480b00000c04044c500f52110b4001c5c02c1c038003161a00944110070800d542841207900ca1031408110007000d005c1d0b04011200d42d645040400980410144a0781e0795160803c02c0049800c206d440400c150006d91030b9194001c000301e00180d0001c1c56080c850400008460f10101030811403800c03003580b20900e0103002009200007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 636415935 1250 636414685 636414739
    0xa0f06060807030f06111b100f0c050f070303140a020a091a0327120408061f14010302090618010e06042d0305070305060f060402090603010501081302 66
    0x8a420420389444419540d140c00c05800040c00f001102248407002400a601c00949403080110712410302c094002d41089250744603e8103440c0383e01000442601c802588070322005c41050388010040c1c1c0c140510064084d01030540c1d084806040440d87d0410706007c1c0e0040210484d03002003004151505d403968100a40220407000002091307604041903040c14800000c402d0f04010240702d0075a590481c1090000742c5c035030500d01000b0042c0c50940032660081003215555200d0320070054807103080a184500c0d065004009034200003905510080c1041c44040100540e010400d6102c131100482006801030300c10055542e410101c001781d5000034043c145100d01140c42c09170707201405940043c0821400c0c1c02a8007034403180c104074258121000a8840d0f60840740e800c610480e41030a82e0302d031200d6040c1042a0b0082e00c2ca038100350200400b811491200c56440390080310210300740354035100402d00c0b9010501aaa0501c41c0420100f0010b11400038507140990740200311000d50007111100d01c0d03d1841394 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 636417185 1250 636415935 636415943
    0xa020d1101090c1211010c11100c05060903041d0c0a0804052503050d0305070e0d0212030703020105060108010603110405060d09061a0102011d0c061c02040f060e0d022107080a0f 78
    0x51412403086d40c419034036045499040851800450151400c0062809101003c0c1c424440401d00020001d0000e104031407050303022074091511646018074040754a0040195072500351840782c2081071440961040d5409406189005645651145400d6150088140002260040e031040b01901015036060103003d072482801030341c03a250440c07602074017a54000d0303884001044444800b0400d5061088100f14054001080644e0000001c15224156403040340280d0041c0d440d1820020700303580060816004244503d8108149003078840441528000d80c01010310503140020790085603103982d0170104280f6000202000100551f10041d044114030700521409542031103e1500e50700c030141200b4030840c26040140a55990000801c9101c2d8442c42c42a00005850007582134400e50300d102600107444106c80511409082210117003500c04459a00792140e80c1d43e07404000140c451406990142c0c1c2c49803401045c243c3c2001000c3c0c10b040d260380082c01c3c1442211102414490142103000043d805 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 636418435 1250 636417185 636417203
    0xc07030c1a09100f02070c181808040501090503060112150632010e09150d150b01020601151b02011407050703020f030a0b070c0f120206040204110a020d1101090c12 72
    0x513000380710240e00649801a0a080c0010f03c1002001c00c00342c91549030548400b400140d840841101100c032030900f80054581e1000490223100300e580004005001d41003c500604d00d030362405d0000c1101404180c001000800310b050130308035985080c1c0194002d015200c0e02010010702055151003646030021291103c945006000a041d50040341d9005440e5030203045005030b42c0c4e6442000340321580c1480c489400c00c1400d6211008624036140820355890440d034049032005440000a00c0c0c11811b800260242c812100b0240d0940d8001010318003000220030900e81241081c00165040c04810800c0c1c035004400040c008200000030031103d00766403084070403528903503610051690300d0700940c1c1c006160029401c04900f0b104e004000d0b034903c080c4503403000d50f8109070564803440b810b804543c010307001d40c0c4a68144001c52620b4001e04446e104076209940c00c00748030041c020356641d40350404000303100c512034030342020f072100790032600f91123400021640f40240d50340b19405244080340015a10050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 636419685 1250 636418435 636418451
    0x2d02120a0507050a0f060c0c05090f040620030601180b0c030d1d0703260f030106020c030c0a14180c190c0803190e0a060b0f04050c07030c1a0910 64
    0x4c1e00100400c107884c032501104090a0801c1001c2d6442c106100060759956074a1800042c66600c01100d2441100c000c0c0300c15011303080500d400b20944070b02c201c4101683e03051401e088000480700e4103032540b0038002d00e0195000500424040d5403440a5008000182d100040304254200000010540325004020400201c0c00101d045070851804452821554000783d100b0070114280070741000e170f02d5120107229281c02030b1701c00314555030340d11400340b800e980c60010004211164040c0324034080400158043c0103141d860000080d00c00b0aa4003851300301c031001168200c0151a41c0006282c01c480d030780321517010390400d0f0100c1040782c0c0008441101107548401c501da00c0a1140c0f000c01000345e0300000c41030454032403800c07800c848136919101100c00340e50380b0b902280d400420440030001c5070240d5400105131070488180050307242080c10840c021414801805101311101003100d415503014a440404109540b50810b0550325451480101035404024040b80c3c600210310781d20051401c4408008140c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 636420935 1250 636419685 636419689
    0x80f210a0e0d080408040b13440c040c1205090106050307061404050904020117070c0c09020708040317090312190314070c02150f0304060b0d2d02120a050705 69
    0x1002140d00801702c4009100c1004204a00000703030850001c0c441d5030701c514603181d06140c0701015204080c1ca049519002c0d500e10b4689207000f6030b107000d544850241068072584101d85955600410100b07024541e2210601c4500e84030311120741d03074000e8100050003c0d040c881f401a002c1c01b460f0040c00d10a0252000004169000300b205030940121003500300e00b083d244c141000f290340001031041c1d05220710444030100a148a070700c160b12602440c0c860140d041881d0800803042201500440d03001441003200f0b4022800b0321003503500303da40c82414000403000d4030800341e04d0b0b4003c000e050b503014803500c01b41218100b200b4000c0c007110404004441640080e000c0110192000480700b146060104004079103e20310441103c10070600140010200082c0c82558008075404030714804241c0780f010051004001540c0a000c1e52a6070413644234000e0306c62501c07118145001c00401d0140324401e101c04499482180d00e8020596400a011420300e4a41415a58640d1034540c4105e40e24091a90003003414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 636422185 1250 636420935 636420947
    0x1020702091602060711150103030305070305060402090325090510080c0906010e060706110c0c01020705030303070f110a0203070b250c1502031603020a02100903080f210a0e0d 77
    0x40b826030080030207403a14141945c990010360b0003501036010300300c0d0040c8540c2d981c2069500840c0310359070001d400d1404e0500101190b102610341e034401c80c01001a640c0f55034000032035034603442311203080c0700340488802c00d190302098545d40542802410302080010441d0b005032000221542c5205031880d11000d00208036400e201183c155000c505031810080e401d081ca0300207080c09030302c01c0034001001401244000016001141c1d1117100c0d52000c0e0f800d40030b55074148071840047c00103070000d41c00d50900700c1000c0d00d01d0042d02154400c0103400d0003204008481008600022038001d4150748910b500c0300c01030443d50b800f43c035540501c0007420300795905020500c11fa44608a800c90317410302c000d07814424648000780c0c0c010221421840140114843c0b05d0422014200c100c1c425002002043d031184184285940090f40c0a814014403450070404a44108110380140060409542d80c0b244c8020011038800441034a008950a4503804c0100400d0180d01240104400744122040304083c02e00071164 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 636423435 1250 636422185 636422221
    0x44b1502030606070b0601030f09210309082d130311030a020f040506030c030712030f090b03040206130e2e060c060f0b120a110a05031b030c0a080102070209 69
    0x8002c041100078080342c0c5e03001c03e0030b402210516000c10803100c1d240c00d0f0019642e07810303815581d03041c004141890072440c944140249540c1e41c10b082c0040070260300e40b10503600803d81494400301940410003038a00b440f0b0b15841c0e081100c3c100c03441e10f0340c0e29074080e000907135014001102c81d0700c130342c5071a541c252800080d0030450590041070145000582400d000240101400c45505481448a00100b50317806000702c10107401e6100d01203034806820300b80100700c0e6034140441005c0c4285001d05100d40108041103c1d403058040c0c50887d13892607003258244440101e40c1c0140d1032111090207004000141d00007000100e0400401503102d95003c98400c0340042c8140700b88008541000340c032900244017500020648148e600c000103103407182c0c03408590b0001500000f4071154124280303050801c4046001c0c840103407002e4415034152400d0002003a030f596611354003106c034881c542c442803031250b8081200f1005080c002e001d42c1800b960f10416a8040e4001000883c400c200b1400090700503c070b00102e6540c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 636424685 1250 636423435 636423439
    0x6030b011103090d0c090e0c04110306090c0702030a080408060610020d120b0402190f0f021f020c101e060b071703090312040b0915044b15020306 64
    0x12400c1c00d80401c024010701489021165041c070141700050319504c900c19240350302500406030800300c01401c1088201d4640410b07400d11400e0078014010709444800b25142c0c041807141c0090394401c91400020320303001c07107480c000301503990004003c10f5103080032907614000d0030142d54240c1120160078082e43c030b81c1000d180c00000142815510b100c141d00e13581003480740c40005000140b070810840080104510100d00c04c00c00308103442c1d00d80108542c8014a4804460144083c0c41c0e05001c05001e02c15410000030504403407900801c1c03c03a80c9403428031280d124500d43c4401007290720f0f01399046810210803018002c00b1240750550000e103960410007241e000a0784101c00c0c01241321550f108a01540014000611601c001d0104c126050340c100b607941d009074050101c9110510300004e110381b42050580342d03920111041c0c1c00b400001080002d2401c0450000c0941c500c03040500101c5c1d00044016403803e03244084c410b041d02c1e00440d0061980707041d540c0070308018285207440038503560591105640c102e07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 636425935 1250 636424685 636424687
    0xf0c0702010c2109030317091011070804060207180c050d0b2107061403090601050607050304031a18010207110f01020f15010602011401120201030b0607022d0d03080123120706030b011103 82
    0x140c040300c4940d11080032b80d084072042504100e6107889a08403908203030003030f0001d42e001c00401d00034070a442d55034044841d4000800d000d405048500184213005d0090410f1160743c03503612000041d07881c00200d09030a00f185400c51540c07282c449140f80e449009105100c0400c0e074402d041c0c1c0403840d00c2c40031070307100d2000c0d88010401a403070842400529800420151040d010600010001800c07040d0744865030400304d4070303d0700c4c20304001c2c94090040b040c0b0a40200103130b20400100340024403443d400510000110380f404154408140140e0900004004183c0117005542014041c0b1404c05035040c10b80c0c8159008200e0034010422030301280c0b1080c007994136040c0070814840010b41c466044807202460141410b81401c1503980405d0300740c403500d444144800421010132000e46485072207007218590440322080d808590340c4024210810600600700f88502c0e505003a8103000c031ba2504da154105000d0100140c0c40c0004020648600303aa01511001a042c80c01c860310310340c0304412041c10507085002031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 636427185 1250 636425935 636425953
    0x70909050708160c0b1602070e01080a050c0a06120b0402091305101d0a02070602091509030c10120504060e120703080108030703080a200409140f0c0702010c210903031709 75
    0xe84144100c0031b502046105444001c03498183e0006424001e080007001040f142a49103459420300800d08001d038060800d02c8820440940d110310820841c1d4a01c04000410354042c002281c043c2c49010801034200c4240000741e03054121550096102c0e090f09107201d03818a0b2548801d2544070030f050303040301d80005000086000020558000c2071200e100d1040185011412404104811036680a49101060104c0c680d03c89013014009003800311404c88035989021601e8201400d0001c146100100c07844d0399100203010850303168000c00b10b1680b481c0480b0340b8060000604000c0e640114000c4002a00ca100005403000c400015030300031540c10f84a400b0943e4504600038000c0094030320303004440081d29a5003a0030258a0000c5c406406440c0c80411141e03140110309444100c0944142050440e520422490b0102d4030250b0b95000d0f42440c00e810b40c00003500f4014505071078400780c6009606810200c0c60300b55003003501041102d00c03e89034503006038180441c0585c400030071103904029801080c81 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 636428435 1250 636427185 636427201
    0x609051002010e120304120f090b07020607020d08091e0d080d0915020d0b0a08030409110d14010509010512071e0b0403081e070c050603070909050708160c0b 69
    0x20031040140284000904600000060744ca411203040c8200615800041400b00740801001c0d003848000036803d008e141550700c08030042c0305801c584a0b0310b041c0704000c10648210360340c2008540039a130300100741c001c80d40e030386081110450340710708034240c41100501c3c0b45641007901c1c0d000500c050b1400030701d07400301030b481d079119004164400d41107116082c4e0b46490756800141c107a601b41400344d2143c1c1005031120b21480f04002150120900300d4464101110104032400000007214151801c9120118a44c00c0d5001d100c016030042e146084620b508020310700c010711082c3d44905040f1001129001800d903a20010f0100b001c070000300d01040c0c0d8110328014008416103a21454411940010600700c050b43c0d4200c0d00e005130019001210f00301000a0014403905003450024100c64000d220170b85031040315907481442d8030451140ca400b8080c003000203942e050184507050000d200c1d000040c0541e02d009603000708044800c075260000d1400703511100d044503101c1e05902c100141e200050803029151004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 636429685 1250 636428435 636428449
    0x1051f081504110904030e0a080a0503071401020903030403030e03070b0406270b0d200a090e1b0726040503070b0306060c010612050c090f0a05040303090b0c0d050c04060905 76
    0x60342c1a43e20030300d424815071111000c0600c144d0280c0d4130058207520240400400100552192500303074003480c9003070701140020003220080c51748059690341315400c0300040342c0607015481c0c0ca260306000108000080c0f5800080a400072a0b003202514a01526284000c503240100d0143e4000503940004002520302c011a1440004028141c2c2000385070f520f50b04900c15500c8148403240041c1c44d0f6501c0c2076500417248098080141d80c0d000107003441178460340104410103d106500c0c07046654000708402d000b100300c0c41e10164080480180e95904582000a1080c03040304003e56410b04c044860100802c54070183c5040d1a80240985019480c01c011103540d50405006607501c03040c10401d40a59010034401c481c01070103443c90f400403111282c10810b0400c0315000820b802025120200420b1201111690b64030841c400c800040ca42c55a040441c01000f801c03400034880254030045c05103044e4180080c2c80c044422000c00c0c00540e441219044090140384184e102140d400b150a01251500c20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 636430935 1250 636429685 636429691
    0x14070509010923120106030b13170d0207050c04050408040b13241706180414060c0d060602030711060a0c0b040b060f010c0506041203021b01051f0815 66
    0x115102c80b103982c481c24204086001c030a25110144900e990350a2181030091001c031030102100c000f00882d40c91500e80380d2018400420510352030295008610401c1610310040d07401c0104007903000d03110803504081c9402503001e003809440d40d03c0b07030f5051461946054003601784983d511103a85410207181c02184525a0410080c1d0f101d03904503040c012803004040d8010001c0504030036030351010b6141c40100904169005500806c1c04540c08040121903121072405140b6119545035014055580b810640100c03040e442081d206406900c0c00d008101071031201900750b4a07100030041002030380d51134050782d40748120700c0000c0003100600d110100518014020386505099030519045400c02556010560041103504607498541c1a051103607a04204a0100d01c82400b820f0103000080740d91501c6a5446004000400300c2d0b115104074200f041c0329070155003240c0901c084c85030306010a1f03602680640380446600341030356201c401610014151144107000c641818020b000a243c02d001030483c184801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 636432185 1250 636430935 636430937
    0x7110c24090301110d05090303070c12031b030506030c010f120b0d0510090317010b1608160b150402270117010602030304030909050114010c060902040905150a1407050901 75
    0x90001c0091920207001303c044881d00c111400c1c1c0d0301c90035158100102c03a00500741030180d91040c01080b45854000201002c035036006403840300300380c1c68070f41c088010b00b80c03030015440c810503c2500c10f036402d60103410660080c0d10850941f8a03040d100d000441d65105044032910019056030b469407116042540f10103542480541b1960f00f211480c2c540b540b42180306c001c0c0846d2195540b5400701807643c4036000110040e0180240c0c0f4042d494421240c085024112207640c0d40f00700741c05000c04120181049445191000401d40400510340c1000740c0e0708a01200c0c06150348143d044510110b18061084912140d07250700c0108642441000b00c41615803d003951605100551034040c40715a0581c103664000c06965005560f203107854038000305030300300580c40180c0762810200148204484070000c0500034000307107080e401541082c28541d002d4070800c00080c0d001483e203805641030110110b184217a00d00490383d200001d488480407182102ca00303210312480e007000000480c2e40e5034860030081c0082c2d401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 636433435 1250 636432185 636432187
    0x71104060308090924061810050706050109050c0a030b2b1104090506011a07020603010906080d02070e15011b0b0618090c010c2a05240702040e0f0f0607110c24 70
    0x9100042003200388d92503d840c000c10301c0400c000702002990b00034540540542c01c000c1c0544d090840a450484c0a0300411209040e2a039010a0031a203444460840300c240c5044440c000800038040455184600201624040134840342090079080600900c0621580700008000585c40c05200b1001c0f0000440750f1340d5440d00420010340980c1d95140614041c00441e1000039110345441c2005107444046014041035400c00e4004001200000302d426511407610842c001030030080c5001250444d0001c41103900b1103800c21062010b025600340100d100740300596a98030103415070701c0400c0156030210340040413688026041480b41d4032510a155a55108550991543c4403565003444100d0513408050340c189110042040725140c00d100307884880c070035854050704a40040e00c4810540c82880c8000e4011903c0f000d0064003082c0c10881e41c100488000d040e0380d18142012190b80d1242e000780e032010002404081c42c4c42040d400801c51100744072008140170000c00c0643c1d07403010f00000010300302442c810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 636434685 1250 636433435 636433477
    0x612020d030c12030b0906120d05090d08070c06020d1106061e03030309010b0a0501030608101a0303031f170607030c020721020a1508070507110406030809092406 71
    0x8508043c00040040310780340403a00340806000e0143e8910002c1a1a00c00c030024000384146403004500100a0f051618101d90340307003040800b14500c0d00e0f509200408001d0005011030503c07a1a0320801d0594946600361000030502c10403c0300c4075514501003204a4100302c02003480d9142000369006160310307c031428089000000000390131500100d0b002243d503511400e01040381d00c4c01e104000041c2c0800d081c2080020309000034655225140181c0c1d40f000b039560505010f04500a000340c0c8680c000c000e04803aa6440e10f82c1484047d0760a815004461345446040843e4070100541c200c961060140000c09541e40c90007400c802070074580960704154082c05d800410991501d141d81c42c2180300b00340c10002001e504d441404860300c500d50241080180a01c0c8003030156a008442ea9040041c91401c941c5500315418000c40781c0c401d044106034000d2912100104001480e805000c06000455403109141e40780700312442e0240c00c9000ca590720342000e0100c1421454081b020301042c6195680310b8400b24 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 636435935 1250 636434685 636434693
    0xb0a030c06121e050708010b03190509030904020f0409151202040914031801120c021203100906060e13200f1606050f0106030b180a0e07090b030706030612020d030c 72
    0x5044407049002c280c80d13508010700f5940081d80540100b00c041c038150300d18503000005807201d00b5901c2010204d691504040f175440305007002a651300040007001107540742c0d410300b8120342c154001d10403a0030490510203820003030400c1c0030b019000c8547c00b085001c030100c40c550801004000c81602142c0d0b00181c1d50041030051130801c0500180c0c0744042d1840c0e03002e420400050504c1000007441403d0606207000d0200603030380410407509000c0c0e0042d00c26240e481c1c0302c071294081c503000d800c80300b03686151100000f0000c2e403000e480703141654151030700d21000204541500580e0b02010b000410800c0120b81e0f8941c0901d85801001c3d0310b000f401499007800c140d482003c603001d170105019503206032550103000c002012145024014181814104031400d01c40000c2503030550b49501c40302c0540b000764005a56854180c200c4e801800700a000d903812551180310b050014165008507601a22414001042c4035000c2d1103070805950b02d41b02e40c1e08154035954200010b00c5200700c021000c0201101d4400001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 636437185 1250 636435935 636435971
    0x21221030903070f1101170405030403020d030507060507080f09150708070302070605090307111906080a0615110d0f0903150207080a09031e11040f2c010b0a030c0612 73
    0x584512105d050700e00e00d200004000c8281d000c11016001c14120512001507000002c4404683d0b058803915801609810181c586009507000a04104d08085c1004075003580445814840c1610b44d102d07651a0b21030b00c4209d031360741c040d4550544010380e4500c04031300c9280c040c80c03580f030b400019458054548000c1d5690300c025944c0c00d0714042d42c20340c00883e1040801500e08801c581400c02941c90b6000d4240d42440344031600503070302c1088280040760340800c4208096030441000f624805002104a040c4800014040c00050302400c083d070045100505a003842102d0028164402d0b9a900c60312a083d9142c0440e001501e058096460354200000030000b1440c0000d0807055115444d4050340300c0c80e40c00c140303182c1d062240d245900b040104400304c0004040400c0d01c240c603881038038000f071559990b00c824001803450f04100c407159804030008411119040e6039a603001803100000303102072180c0906100800103140402002a000c4480602031540b0801d03820014200702803011852900800d80e0300d80c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 636438435 1250 636437185 636437213
    0x21030503070305093408010903080f060103140108060a050a0606271703030a18082b1d070509010308030c030c0f0a0509040c080705091c02180402122103090307 70
    0x20081007001c00659201c100340017000200301900c001c0c010146103035402000f5a40040103020480b4040010500030b91280c0e108201d441e034030300c0d501510303075131240b0398159580720898071891254102000501020018006c1108503031031515800324040588000e40000440b0441e50350305000030303c80010b049107403008003070320b00c102d40006103070760741071507050001980c0c11301e40c0343c280b0000070044102c00602c0d045d0455071003558482d04c2c60006100800c00318500d400d6a4a00803466050168200d8411611051510081d540d10b003115030259403017060111403e003d12024040600500005240c00d5100c002144c0c00320b00303408500e14004105881a05541068a11600046000c02d50b40e41c541454880c5d002d00760b080d428181e00e9031421a400038003e2241840c1e250040004006554130150074100003c2e03142d500400c240c0d031031800c40082e030041440480c0c003640324030504004d5000c400c00110710600e004035030344810a4000e08000c00c40401d41e0024110070002d100801440300828841802044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 636439685 1250 636438435 636438493
    0x1107150f0e0d0e1906080f1612110c0f0c010314040b010b0702130903020604061a0f040e0c0d060f0b01050a020309010f1707020a03030b0a0501050d0b0f09010b042103050307030509 79
    0x146509000c42d9568448100a14050103210f9110030485040d07001a403403411227003c10008030700000c085010446034020f5401c0c2410620400c0842412042e002c81d004071164400c0e6020006200c01c00d02001c81884251406440d0180b040d0052100c0c5141e00010701c0c00c0fa001601c0511040e80580d94241150441c85080c0c005130041c906010400403240901c0419130244540000403c840d40005800b4002d180071113481540d070b520403c00c0038001071105248a520080c0700c11511015820150060030f0401301d542c981c2450031041c1546c40d03010b0f0003507901e9480258001c508101c8503000640e007401e02c141d44541406800c0072061000c40a01c2d0401d441041c00ba405001d0911880c1341c00340644081c0d52100d44610064401070080c0d0364040d00781c1e81c4002d69810302003240c0110360701080c2c49021501003141c100b201a000403440c0e46902001784122522400d03120446001c1d030903907001e18202030780010000f0b8820008074010b14866000aa004240c00301035680d9007483c014212050450382107104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 636440935 1250 636439685 636439697
    0x30103050703060c0921051204080604120809121305060f0d0f0b03100f1407050406091a0d0510050310200406080f0702011107150f0e0d0e1906 63
    0xb00c200089130103060b400c112241060b0300682c2c1010051007138032a44411014184001c8a4482c062040c10440300001c80b01c2e4016444e62541c4a041607a01d4110849055503a1180c02c0300041085114022940c07082645002812041910070b10011085d48010004240d038004110003044a540b88070040900b103200000e840d03911124400e509042d200e52000d0400001d2603e00c5200c29918003003880191034641d0100028145540c81040c4000c00c225902d00c00607803035035000c000305150004c0040041d42d9580e01c405150f1660b074284020030b0b503013001c0c002d68413140a2104540d800f00a1f004070350405240818191a151a840824581501414541c0e00ca030344270000c5100d1b48800040c15580440b940d0b030068a09030421401600786032003e00800f14180c80c960005410f40d200390b01152619178003404150f60b0305014100320482d280d01c00d82005280c0d28041d00080c0354106440344034030710b203403200c0a843c5a420780d403419034542c032504032400c2e0040c501c03101d8181d00c41403550321040a000355403201 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 636442185 1250 636440935 636440939
    0x2030a050613090201272301080f06030c041a03011505100801030807020d1b060f09150c0201081308070f12020d0903120908030a09051e0112050414030301030507 71
    0x80e003042d2001c003601c407600d031030329040140c1d0b07105104030a8401726445440c142c8241d5030b102e4101b0700f070340c0d03000b0100103400c20f4080c01001c03c1541c101d40c7e0340d81c2c01d0b61241a10340705e52094150241003598805d50582c03000001200d24102600091214414981603501c580006000b080c20740e14946030040781a00010010300c0240380ca4109402015582c3c03600c00b4007076045985040c020321413140003034810069000500c0c10841031001d110728401300b241c075244103555520350240440e1001100400408d01c03102c8080345024805600c015090081e944500c0e034001203400560b016940586480760224103982e10340e010070100707002420401e1140c1f222052070092030900314810800c41c5c0090701190055414040600da0181400b800d50360000c94030f92050030104825103504c180d943c41101d20380408034060314510b401240c101d0443d4420764001000d0312884000da00340b40d00408034140800c012000c2d40c1c4102c1e0f42075100380d50007442011800d840c0c152007241c041c03442d04241c0c81102c41d54003803441 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 636443435 1250 636442185 636442189
    0x1206290a0603090b0a09060e12070b0f070c02150c01180c050604050109090b1809010207030e060306010c06050a09080c1b0103090b040206092d12030301270f02030a0506 74
    0x34400610240c60108603440c0d2503500c44110040280010640f1500d507001182400039552240c0c594581c200100ca03003140160017055034641000e58299444880200001d2040304c0014043c1c2c07084149503180b40c0f19100b66401c1211650b4940b01d965025070052002c01c107401e50910414441d0381e914001e800ca076a1840c540b44801082c107070031080c00b172081480b04205998000410300181c0e08142d401007088044840490a081d28189180c1c12a03d514000c0c004003030320640c01400b07020702954403a02d0305c1d0700413810b102c0f82d44000c0c2c0d07100e03001403450000c00c804034a459010075001107076910301041e44003894680c01110b421176252055150050907049010b400074040302d082e844001e00b414800e0032101c0e2101000d69000600c003a004810014001c80540d68403419017030802070350b625a00608004440c548002d0880f07118250244801030041001d000001081d40c1c101c070021800044003641002c94103100b0302d841103210f041240c450110703042002d01800550300c50800404000740524114003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 636444685 1250 636443435 636443449
    0x60c120c0c06052d030112050f06040f0506100503100b0a1a0a11060403020307020d02030a06240902030603071e031a070806060702090103170c070b0904050f0907120629 74
    0x401640422118994100d0040d1380e8019281107410162070a10501460300f425400d06060b501d1004803806050104401c01060710032500541c0d02840c220f41c1c3c41d6680c101d2403c02d800c814042c055140c3e010401894800c5450341141440030b1014216001c030541c0c0e80003d43c11401031410340d00045d040410b19130391860b03100908076456680c0300001d01e0142403580f030107916440b85020190080c19100100750954a0800541c4045c07507018008100c881d00344a480f0400703954080060070054800310001841c81080c7c000d0301d002d44001400781154504d080300e070b50120301201e20810160009081e0000c082030110101807604104c100190000c2c1c40e09180081c005c02d40200b0441c890380092001c0805600e940c2d2000341503c0c4d0280307090590004030758549076980200c0c11030f01194826110085610040d284c06811a840d060b9824030507a00c030110b804248020481e0a801c60780c1c8000d408204d50034072110620300e03950150304001514034068030480b030002110100c0c0c550b900c408945003070103410186 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 636445935 1250 636444685 636444727
    0x1e1305071202100c1728030b040507020c01080c0d061e330e01180803120a1b03050718080c090c03090d05071703040515060604060c120c0c0605 63
    0x460300d440350f58440ea0380c1d01005c00a01c80840700c0352030049000d4a24800b0403d54550f0004504410700c22948100c50050146c41c2000e05603005906240109103200e000060044a0380c2c2d05844100741681c42011250740d58001000d41044203407a41000240e26603507820046608900c2c0c034810705214109840340702c1304182041c4100001d464035103140c214050112107503201481610b400034512401034012940c5a0588800200106460f4000101402c00100034401c0f4500202d10343d405a03075440e5500215146075a0f81d20b6104090303171803518500c0c031942c08190304c00400e04015036254a0700c116000c2304801a0410080e0381d0066900b80642e1410146003503200d01284d10329480c614004002c06d443d01d590b540c0314024000301041c20b0081080b25003010050240003010303580c603031600703042c0340d5504e50908080a16001541011824038200f100c01c48040d18401c0e12180c0c0c00e80c02039030320501524181e5841c0800c00407929046c1d40052103200e8018000c210581d03c0a03110095200d004500308106 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 636447185 1250 636445935 636445937
    0x4030b0906061503060d05033606040b070503072009090615010f050c010f0623030a1104090b01180e0313030f020d08040806100e1e130507120210 64
    0x680070802103a0341e07a00400a4252100c2110b43c880e1200b602046d8840d06262009000d40000700e50409251092600310121301000c0d1030703520100c0c1c140d00c00b040304039014150b0107030000030810090026181c15802446418440e5003140c3c986555512055540e00b606a4007001640080b009031001d0300e810501c0940212500004d01071a0070080081c400c0c5050480099040c00703c00000c00d0103950003442620002c9252100a000300907070a410000200390502a00d400014900400c2c1421403282c3c14903464002c01400410030300800d52905600030b001c3c2c544040d40325445407c9100003070350641004d4001c1044458800f40c0c01d44501c108c82c2501e4552552100a91042c40100070784030031400550110380d00490403d003044042d0000c6140420706503000b40503030b01d00041c001641e5000040251040c02080d4000e8849a141d000c0c20380c89850544240f5411030803544501d5020100d0400c0c03d821119a011603004204507075205800c1250b942d1140003182c182d44041c6003981403011001b1140812 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 636448435 1250 636447185 636447193
    0xe0c03010626160e040b0d06050c041205100c020f060c0d06030212070e010b0c060c18030a0b160507150b1f051b032a0312150102010f1107020f0d0606030804030b09 72
    0x9200c0405c40150640e4400b03010326841e607022a10001180b802c2f43c016041c20030304080c9403001810002d40c0c0c0c641c0041c03400b5a452400049400c41440820400c07042419a40907288a49030f200c50022190084068990f40c0382d41d07454000016030f00d5a9182d0091035850300a040030f03624144030003003030050590100d0400343d020480410361617030204103545e10285282869484503040d0303d02031003904002070f0190309841296850f02c00d00c1a0f9041e00c51180f00d03100b10880358412201003c9401c2c0c028110000c0c1610700080342d54030b140780756420400e03542c28090440c0e901c245111803071203040381280e0081c0001c82c20000b030b5440c107840f4000b411020741540c540110300c0e0900002282c0115811103880c80e42505c9048462000144240b0480d00301703080b1800750710310606041801500c080c81241409d400340d860406171282d0806140078004c038202d45056128200030303007a02404460190000c00e9944183c04005900010b04148240d0002e1409112055100c0d4110f242c0400400c4003d04280384c01d0344 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 636449685 1250 636448435 636448451
    0x41806050a0b0a03090f141b010323130c09020405030705030102130501270e011502010b150a120e061b0708070609020f090a150e0c03010626160e04 65
    0x800d15007210f959a40e00d00d8005184140741c10481e043c403480700c0d0024a04802c1549003542c10900003141510384060080c0e105200d0359280040d8101e8443d40500d00f0108403c2e183c3d05c0704540d4611a41e030340500000e440f001007a40f03070307030703034899824129002200307016400715040c00981010000b65003e00b006400841c504440d84910660701c100f54480e5a04100f11551640920342c1b01122018400b0350200c0d40303180a94944010311030300102401556401c0c1c3c00380c5403010b056071050003800d4040364082c0440c0f0000c0c07030940701e544040c1e0040b1129001d005940701c85100180341485004030030810744029104c9424a030090315403a07007050340c40c00d0301204140003020215007094100c4000319070243d00017510b1819480811841c02d488045036600100350010819080a19001041420006000b800009807140302401d400c90381030b03910b15004207060005011244c06030b40c1c9900f00c2c0d080e809180c424000d284106440000080f9180c5442070750414400d2041904002d03d40042002100c00744034100d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 636450935 1250 636449685 636449699
    0x50a0c030b0d0507171009030c02010f03051303030f15080a02090f04080301050d021f030902010e060c0a170c0d0903060c05120412180b03100f1802031b041806050a 72
    0x18071034021121004901700910440041c10000c400b2010980d40042c481010380d4140030b09400300d009026804101c601d444010ba451080c0308441c80341542c42008030a00030940c404a009004811520424503520078403000080a8020001d00500b03000004141048951041c065031a0015045c1c50748180d1410034000020021070650f03054034000d0b0740c0e45041c4500c500005403555804400000b12809590041d00180d6050b0000c1110341d0007070720380d564902c6c480d206101c0b00e0311410381820030300d030420401080000c82203264190304243d0103803a0780c03d02181c09810750802510404d48030100f51945001c0007006414080c0c01c003045414284541040c4d001c5810180003a4006e200034400c49013540392815043c000c00300c40030344009010001054540f2000c0c2d2a00c50f500c16143c030480400701100c0014408054450350b000e443c0c0d0141840880303407a02c050b601c0a500b01502c0082404205502014002c04c07450241c0000d260308a01410780d0039800c0c0102040b43c0480d00424042d80c0743d0b110500c004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 636452185 1250 636450935 636450943
    0x70b04171b09130c03020402070308090705010e01020c1e150c0d08010515280e03011407020d11010605040f0c080a0c0806010f110123010902180f030f01050a0c030b0d05 74
    0x104018003e50306801c8524100300900a940c000075880352000c18118189907010034010300c20741e980350445100545900054502c4500d20302e116006911001030b521287c10900d440c074a03442040c00c05c00100180500008445424010ba41c0319000400318124008920400407280d9284950501415550420700410741d80f0561000c601e450000c00030341d0503511a4400043e00003044144000c104005010301d0081000d022280340d46c3c825820035600410310851003910f20f0080403560014010b02c50000001c1d10804603118215501d0355807030000141d01d4845000c1d503090300350742c02800111607980b004050800307900505498060b5280100174046560002420b90b0030036000d082c81880103070304800498000d101e120b0010070301d500341403402c0405c5031421100d5240407500c820341c10013070b0303280e01d1500100c0c09a004600481d4403520745000b007904050010a0010501405990340d03241ea0045082c2514001c0e00c402940c50740d143c0700c2100c2260b1501c210080c0304001c40e070442c5a50035588a950390b03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 636453435 1250 636452185 636452191
    0x201021e12060609010c0f060e070602061005101107060806040e1504141e0609010e0d0e130f0213050a06091208180d0b160302070f03030e070b04171b09 67
    0xf00c02c000344240c0f60707078000c0d40140300c803a0303005808541e1a6940d14201001c1d241e5146c212a251241441c0403410500104000c2d05c0b074031000400003c004d10301000c12040040c40368040043c00580e000610500c142409981d01825841d15440201d00f003403014402103c010701141042a004003800c99241e000700021a600a900102251400f48804080c0742c1000040604480c80d0480c050b02502480c80208001c0c0c4509844c90003004500710742500543c4035840303074551710006400c0aa00c4207040c40d0000036030f820f0b07034285800091030710803d00540c8100c0c2e21800c403c0000903010a01000745241c00d00820340078010615100701c1013880c010404040011780d031801449440702081928050340d15110003040e90600403ca072411200a081c02d82c8030140a46146841c010f01c16802102140a4000c491010b43d000b16080103400580d01c0450043c050b0007903469150042d0540001c44140d03200c007610103051b00707000341c030102180c283c2800d02c0d00280800b200310b041d0240000360710795034440e860130358 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 636454685 1250 636453435 636453439
    0x7020d1e0c03112a0604050a17160816050307120b040821100501210c02070506040f140420071104020f22030b0703020d09080a0201021e1206 62
    0x600914074040e41c0900f0802d00411182c410305004540002c1c1106003004000c100b840c03c0640b08200c0f00c103101440c485d070b000740d6401c0542c01404011381c0ea107aa041d1203451500744151050b004c0d0079240035070071448507403148440390f21209400c03241ba20b00c21040750013090214010100c0515120304142040b42d40400504401d52090005080c09517990482d1003d5581440d402540301003882c0301d55040c8016a4a90024111428007083e076501901700060721900703112a440c401801c800403200540004e01100b021409080400201619641c015201603d6101d21480910f0b042640103045c0a210f0070086102c2c604244001c0c00015003c444502d085900301607942e41e41011342803440c0d9402441e00c0e51500a44005104242ea5280300094a030f01c400800b140a00492010040c1c0100c0c011400040c020702140030101c3d985900030b50051401d030400707034404600c028040d1a84411900040300d0000981d40000c0d07480f5070f506019854011500c0d94460443c1084181d95089503204c0000705564 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 636455935 1250 636454685 636454697
    0x10020d0c06060504050718080f03070b1302040c02030a1d0904080a050c030304060b04060603020c0c040c09080f060f0f011a0306060d0e0114090f1b01090f06020607020d1e 75
    0x6000c1c0035003500484040c0001034020300890500100051802e071254040d201d9105c0b0504011401700800708441c919000c2000095040c15015102c08260180140492a00b1907561580c100140c41c2e5000340a20f03076503580c010f1a1101c1e00e010003c0d044000c2c60864100c040f00c1c50041c50915075684c51210b81007030308110720503100c8038091019a240d110f42c4c02c10ba4848d201c040104001c000094203c3d00c0403c200392404d00009030743e010281d0590140201c202d010ba00481210656424540d1110380c4e01d5075036240c40c0f26110340d1000080d060003103600031312580b90010310402c020122805403a6400c001180b9490005600d000011400100340000040c0300d1103000020038200d58418082c1d48a9800b501000c0014411017841d0600a000300b05582c0e01c200202d0f4001030500f01c000c1030101840c807010002d040401208100e1520032140080d285040c040d918001091000001c010340c0003a0204c1c0c2c001b441d403820302d208040d240010116504042161a4540720b4400c201c24002c0030000d00d481c2014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 636457185 1250 636455935 636455957
    0x10f0e0a051e031c050114060a0509011103090a0306050412170703020307120e0a150b010c02130f0c05030a0b0613060e01090b270405090604020d0f0503070b010e0610020d 75
    0x2c6003544568603004c08040346502a0340d842c1c15055019074100c8006200c00501d04810206000090240202c102c02140c801d2240389420b5010359207011550412000703aa180c000002c5c0020504695600160388680c0e40c1d404010401004418030244000942003480d11851004d8481c2900c1c00d00401c100300300754000c40422126070150084468080384644280b04074108000c85030761781d083d035284c00d0b0f9051000360883e00040c0c880384142811501d0603035400603003031030039001c8c05541103600495180096450300c2254040745c55100702032400c0b00300e60b141643c9080640d040c030309881c1c48190361441182d0800024040000205080080b034640d401c1901004809000503103e500c030700d512208224000045d04812603180c100c5680203081134010024a504507002480f08481e0708a0300b040040e44506c0224001d490304814400810b4404c14180c03000140c2e80e41c071107085410040c0200c0386050820010b00401402c06100e03540407a080c2d81071000354030040c10003990303820030740360001c00c3c030401c0c02103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 636458435 1250 636457185 636457243
    0x50d0305210c0a0f090e130201142d1602011d1f021015170a0c0807050f090601121e1407030606020307050304060806010e040e010f0e0a05 61
    0x39961000844510041468600b2141e0110741c02683e040c030020781100750a402e402d004501c2034040d125401c2c40d880d0f59540d100681c10415500e61002c2c1e042c0414403400e070003811008402003c00e442000d000c03c0e034042200b0b044003040f16100315800c01145041c429100d00101401c116504540c0910340b20440c02d00144045441145541410350040c1c1e40250030241607524080e41d1294500542c21a42d54031200600413040314501503030b444082c400454204882c441881c0d40700c108140301c60507205032510a0395042d00803c1c1c13550011000e500403004c03c01031440c0c100400c100010055511000c9407070400b00080c0340b0a640032600981e5503a94903455840b642e8400410359508a44404001c180c3c1e20780103061041108882050009003008008104948003105558a060340540114101800e081003583d10100003052241008080703004010349036560b0080031603505034880005880018081110140c4402c0c00441049034001d03049040001c2c03001501d9862280c0103c41c03035182da404564 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 636459685 1250 636458435 636458467
    0x307030b1f03020319051608060c2503030b1305060105090d0606090c050c06013206090604090b01022e1d010e0d020f0703080a050a09030203030c010605120106050d0305 74
    0x41d40600c0396150003420314200e481100038942c00782c01164400d440a0f100d500307e104c04c6001c0c91046811000108012001890240c64941001e4442800241484040d1041d401e035681007540003e81f1170240400c24144410750345065050302000f44614613003c000a1320320300c03070340300018041d412403601802403103072561116000e00000d000c1400305010411005080e604030340349120181c0618800020344022908045d403200140404010042084100e44101401488000c41e00100c04002090456076250010f20207007500700800180c41d01070308002880d1906002486c25003c880c251031000c180072113803081c03800c0e022005020480b5449105000680328040140c000740350300309582661340d03400c045158120b84c013031070b4202d0f4034842c0c400400c5681e40a1512010b400c03007008005900c000340c4240010081c042042c01c15612143c1c0d243e022a24552007e031510304184d55801090201d4640315922008010403c0300034009107040c440068440d01c00c46900409200d00000c0305a000c41e003940c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 636460935 1250 636459685 636459689
    0x80c07180608070b0403031403131a01060e030c01120f090f0c030b3303031204030e01121401052404030804061b0c030b06031203011e050307030b1f 65
    0x80041180100320141901400080c080c56090b8040d40c0c01c0458406103000c20350701200e815580e2002c040805843c00007984e4806402002d01d540070f680803038085034680004480c06204410811003c0d0f02d000001001031040ca000380d48203411265038075025070390244150061140c69100000d10383e415001800080410311802001807041c41c100b2030520801a440504880c080d0110000741d03980d03078000781600b0784030603e820414070411501c072003030140e5062020f521101c00b80c2146d02e060115455904501c401b20303001c90004800e0f078084207465900c0303607121580d849464005e101c032007a00c20440422400501501d4000d001c81c0f5060a8a84464540c801d480030114120702e0b611600c90070180ca05510a00032400400d00148a04140d120300c2020002e013540c10043c61841c0605603a205180910060044c96040c8540000648071802c190000c0d40241000514080c195648800b0032980135000c4d80b0840c0b0a4014100c200040b81c1e200301d00399404084154103016412200b8104100c003c555 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 636462185 1250 636460935 636460949
    0x12110c091e0108010c090b040b030a020a050906031017070f140d020612011412030703080405010b0613051002060f01060c03030914012901050403080f04090c081f12080c07 75
    0x840000f030480320650201c44003c20a9858492603500c50071003280c01d124501c40d0008508013080014404000c0364040c059800c11850302034940f25941c00000d2440d0410748285c8201031200d007040043c0c060500308545100f11a10280401501d0144c602c130040c0380f5841500036550300042070100030358905100341802079004204d1a03e0307403c200510755a0540900070788550300060060941c0c035241c40064140f43c0d0b80502d0086103000302c2c0d40e07000c84401c000903204039212340d04c40c448504141c0d1608040c002e60300141d40084541c03880c010400100246070383d04241950404004c2c8014490704000306410350703150b402d240c00700b81c5084c03504400403c20408054829060103064942c451b0064200c0d0f941d2a01010006040d01c4484112070000c4c11000c0aa5002c240108000c10004080101800a10002442450925603a0345088003614007803900880020007800c04c100400d0150040e48134a244c0388a1507a421900f84120b045200e200001f014140070740119000000c040104003000c060104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 636463435 1250 636462185 636462241
    0xf18080904060f0806041e15230a090b130302071205120d060512070b22030c0b0306090a0b0109030b06130c08010f0602010932010c0c12110c09 63
    0xd1540b51039150502543e04603038001c0b0407030f0324968500740b10050b07030700150b0018041c18910000003171000c014044000c400100e0703032400c00241074102010002501c100ac24020228104406240c081a001c4009000d1004030008901e00e501280d0700180308020b890041c0b2082c22014010708003d0f291a030044068509200c00054001d02c8140c250003400840f1020390b1a80c0c07040340c5102c01c0315240e050320300803414110414810260030012000c10107110303403002400569401c2e201c0d255030003064002c0e00040040d040001c14045541401c1d800c0a45c40804400708001c00b000803c0000c1c040000c2c0d12025091984c19804244955214100021196240c40382005800002c89026004007400d00c500c2c404210101300c001600c2d4011302880b60340315448070600002c910302943d180640c40201d941221030320b03c0c1c02c88000100780c0903c076058000d180740c4c0b5007010b0160546855003c0c005208103000820040c0711214480c004001424508103030f04840d54035055681016007440e00483c2c6d070041c00c201c20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 636464685 1250 636463435 636463439
    0x6030a0b04080702011403070c030806210c18090c061b0a03020a050c04110306100504120c050f041b0c03050c010911180c070305090307090606120f18080904060f 71
    0x8034610007040a54130030380728904c1d90210941c0b88502400100c4003030b00415841c000805c0020312895032a544610020300d80301c050903003001d0482012014401e000e28a5020001844440c501810165030250458168104038078040d40c0301d80e03c9806c07201c1c01074001c01000c03174a15200303034400b0180d4444409d2401194050038440c18020350b00c0714403400a89150048568590503410940150a524410031400602d1f41d100e80b001d02481c480302ea800d89041010034031011a0328002d8442d9840d507030f8012400840c1c1141084104014042c500350f551784207529061810b0f003445c0c596010780a111401d4205820f80d0900e608003aa02c1d88141880140c440d440c2c000c41d9420024511802142c41714144c0d881c103c42c0d0b90b40301c0c00b01400d490595842d60444810721030f044c000391264009001a01380a001c0c0c4d031000fa901d0711a10b09235006504500e02140403400100341c030240501c1070400220074002c0500141c103a19401401c204c00260001e042800c000a80000d41c0d10342e41c01c141b000301940020a03c40e16 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 636465935 1250 636464685 636464693
    0x2030d0807261902250c05190f060905012a0206032703040f0302100c151a04110a0e150c010b100809030a030903020f0f07060f140306060306030a0b04 66
    0x50301c00c81d440381030f003140040042040c26451095600788000307408001d81140307580540158122a2010407104491400340101c1d45481d00e691018481700021400203a5500f00341000b41c000409400c03440c20002414000c1240703070fa0021440054151000303092804915904401c80b5200050134065004039000062248000c0c6400010720301c1c0d215641c0105507540d48001ca25244d01c00c80c42555180e1450f00310500140c0b40100e82c07002814500e080c01c0c118070440da0341e0080d54084840c2c540e601e0540d01c000842d42c1400c0102d104a44c00f0046804226a4403403141c203056074040c2a1122041080c0d40d10f0001c0c1503142c256224000782080e488007511040c204540501070715140803a1806554210702c411a5540118007087c09901d0013006103081c0803106900701c0c010450b02c8015421441102c04c41c1208100034000b0040008004000e03007247ca040c2800548003900c640c5101c0e0402c500d8208400d9150300792000d490b08018202c41003542c82d2030380c000007458000700a00140084440711306200c00c01c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 636467185 1250 636465935 636466007
    0x20f031314190b0a030f0612121205100f0603140a0209030309040504200d030503070e1804050d08010f0e15040902150c010b060702030c1315030503030103060608070302030d0807 78
    0x401c09540c043c42001e140c2c903940340581c0e14612600c0c0b0b06400780a0b95000040b500c050f0010b424155282441d00e40b494400d041d402d170b07071041ccca004d8941030742410180031000000c48140082d04003400c1c14000621004c2c442c4020217002040301d070000b82c2c003040b644060f55040c001c48041c460014018841401c06007008414008584031803880b80e036001d20813101c44d003401c4000f00c040e250152503440c256900d8100c113480710304580d0784007503100040071540c0c00981c00d8513041070b010701e004000401e0500c6403000082c042c0001038021090000441034104101c8a42115090340951000760200f40c10002c030b0007003000307003455410080d440010400c140404080d1540a0160800114002d10240340341409000c894841c8040c060f4054020301842c4c0410b082c094031028117a080c4080000e030b6610185080385180809400407102034000000400903c40103000b9640908858405000d203d459603000943c3c650f0f0028000080c8016440084e00c441d00880400d130802e0307144114416840d01c0c22801c2c41c12 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 636468435 1250 636467185 636467197
    0xf0f0609010f0c02070b070606122001020304140613090204061d0613050d14011a0102100636021911070b0f071103100507020f031314190b 61
    0x45600e88090510303800441c3c000d6070600d01442e0003410f0307034a06210b44041e09a1001c1c600741c4000f03483c0c120018039840140d0340340c8102c5001e00c1040c4401ca035804271002d1042c05000303c42c0d04541c810b10003404854524611080e80c070000b203038182c0d40c4080090841426412542c040e64400d40b010400040ca5038018101c9a1f0701c5c007202d03261403601d45120301040680e00035020750300c0325828000c0052040341802d0391482c0404d0700400c00e051f0418880c00d071850070360b07000108440080c4200000290a0358041220200412604206000941c01c110001c020f44084103010603040c1802c0000d4091170030000036421050341445000c1d913803806011050220450356501810004500010000b443d40e00880c69109035841e10808078600064007981c0100c03500720303110a840c00c041540c0480440c0c0c0e410803414411104000300400c8030302d0111006810804000e0710380f115600f04000d143c4130710700ca4691030415554448000f0402c854404086841092205032a072030700102c0400114074694120302804cd = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 636469685 1250 636468435 636468451
    0xd140f18030d030606122c0102130803040609080703050606010509010c0c03080405130e1c0306081515010801030b2409040501090b2404050405121308010c050306130b030f0f06 77
    0x1b039000002e40e542421102c101000f91440c5003101c502c03c0c0e6403110701e000d0070241010000098100700c4400c5500a42000c02d0b0b00000300c0c2d600c001030030003040b900102c401300202081e202800c4207504e16211a40c48030780061406040050002c2e0303000320350f80902504924a0340008140540c261249000a07655129004a910808903503a252500c3d00c00d901a040b0709100c0f0307102a020f0301c1a1200d10511f03001c2502092014562541004100aa0104041581e5151403050074b00782b0300b0811078a00700360340052215410030000100602c0418000e421082c1c010010521021103070307000700511544910000810f0394401d44031340c144011b01505400c10b0249070b000300d5000386603880360a03445075182101080d03034800380e001d0400c4044915042d4000c90703001d0302600a4a107041600340c060000d640c0305490782c640845242c3d4003404a03420920420400805509003e45181441c0000a44410700040c40044054940308500380303581f81409484907040c201d034110f80d881540d2884c10717a11400704a0b0248 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 636470935 1250 636469685 636469697
    0x1020901020615030c0d061b0e0f01030606050a0e060d0504080304030e01020609100203040503040506031f050405040c03060b030f030d231e070c0c0e07020d140f18030d030606 77
    0xe00082100c03030f0400e20900c801802485140350384410312810090101d13050f07c01e29a61081e800d601d022903c0aa800b0100c4c0ba0b071481403280e02c1a0402503400c294802c41e03410146850018456160060204c40103c1e0840c00d0031382485800c1e030000365140c4550f440042c0c02d07500345020700c001c100303103000074502542c42070f2501343c17021030701038012a51903c1c21141d081c0c5030744c000700c1c00031032010f0701d80c0c020b42d0418024400d42c1d1516407034101084650b88243d0707205542c40c80340c0344c0d045094204d0005402c00380c4030860781803215003415143d01d10703010314038080034012942e242100c802c2964104140040f0f41e003450162511103096501304c01c000c01c1040940c54006102c40c103200c100111120006101f0100b0068000d030150403120500c0d11200b00905407001e01080b0942c8401152141c1e0611005111080145200340790400000b400c14414002c5281888200344040b00e400c3c11010030746100e40e450606a5841d003e4a0f0f080402e10315108208540500070680d407a11156416004803042d560345480700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 636472185 1250 636470935 636470941
    0x1080a060f1418060307090b041d060610020d0801170a1506051813060504021c080d110c0a11041d070e012102040504020a031a010515070314090120010209010206 71
    0x80f03d0220801c694035503158010b28400e000c0310201e42d100c805004005400040c50300c40c48840c0408998950071904919440101040598500a02401c007400c600d40f01615094242d03010182105c0c1c0180071741c00d030000200007074030759000c410001004c0583c0c10507420140080c04c610450001c02d9203002300d40c003070402c2003040307004403402403145030060300300b0362407071458041c01d0310307000001c0c803000e0812688403a041c0d1a00c00c05034003a895190b0700a0298055079074910400c006541159444152400365601c1400048140030012036081400354110306400c00340d480c0040014000c0682101010003600342e05141074015800080c40c5003503450345123214040c0d90b03c5490075030004c0c0d20050026000043c240550005040580040d0f80041c4040c201d0100790b622547c030392403a08500c4101e83c0d03550b101075004005c20301e081c7d0103403c24404407a103124580226a10001d003030070800740a0a4001d84c0004240029074880c174480080c0600c800f281000c1c1c1e81803088202d010b54090034085005120789008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 636473435 1250 636472185 636472219
    0x1118070e0a210f0602070c030b0901060f050612070e19090b0103060b0304120201092a060e06040918020a171515090601030b12010b090f010e0601080a060f14 69
    0xb110051440101c02403040090955031070941d0b80070400226000c0782c00744905c0c8000b50310200154091481002c52a25914280d822142190040e502a400c02d00f0006810000c40d240c000860301d0b40300c42200007005030b0740d4800c000e0b500500c08144c0e40d508028102c40380340d04880e0302102c113003c1c0c80540390107005848100e401141569124043d00102c60030802c0450001103070180c511700710707680a0001103018011521000302d02014400740c445180050b00522541c80321040d01c201c003411107030615985442110001c141c00e0b001d140240e40c3c000356200b40509611040222921600f6401440070140c1600d401e0000c0c032900c19100d400301749201c1c03144180313000c0d10030201c41c40c401c20240c1c000c00c0701c070b10b640d00801034103542c090a9107050680d07c0080c500241ca41190704046010800700224040070340388103000c4040001070804000c0b2040d1700050151035034400080390001c60900e40300400c2e4498500d99001009aa48941174100f00e400c0c0c002810009551819090b4204980c918132003003034610 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 636474685 1250 636473435 636473459
    0x1006090c08010510020a0204060603051501091512110d020c0607050408030702010f050d0603060b10021b10140d201305040c0c0b010807080115080a1118070e0a 70
    0x2040d5000c20030380700052145003402c0c450340181188030300c11640407032915000f0500b200d5a40d000030300060307101d40412000101360401407900090a1034200f154500e000501d2200040095a000400c02074a00b5110b2012844d0004242c8072010ba51255a404d10105640025845020805468046c02e80010b180c240108140c40490340c152020314903040d0103034011100f032130444241c202408414451100f0f442624402d0300040e52150500041004c50319081180403094100b8200440d408100b1481007540c44105812030503405840f003281c40742c5a41c0050710b01014034124248007840214000d00618040c1d008500c050390110015030090708005c01c010303031921459216a0000010f0740301040f2504080c2d001007031070b0107240792054200302195200001881c0c00c0c3e03c210035a40c0720440a00c103901080c4906281d00e022000190400c80c6400e865580b0340c120b441d80600f0325a00411403014589444c03101410010341c1c0382507600c841c900854060445800300308040e004d04403408020a858003d1a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 636475935 1250 636474685 636474701
    0x503030f0d180b07200d030e060901180602090111030a0903061103060d261606050f060a1202130603140d080114040203180307080a030f0204060914031608100609 71
    0x80b82e440200c4d603c1c21400d46000d0303907040780d6000103010b4128019032a50188425064044540c2e00441c070101e0041101d4904171014000700001c3c0d140c0040d103004100082d0f11100d0b02e9500c60405600d03560b0715001030722441e2408080e5101c0b400000b641500440e07209e4600e005a0380b04903010000072031031090141c0680000c581a81e000110140c00c8004145407000c3e0300401c071244c469507252031102d0040c1c4161038000c41c0702c0340e00041c10500c81808000f201e015140d80210346100b808c40c0b6240440001710156802e104028000480184001c259103401500300c0105031845400d1142a41e00d141c40070610110b0f0082c2e480d2401500540d841107841400d966040380c0c41a2088020300d00764000b084020740c401b400070700c5242d903a200c441851030024000b400e0303d00c0c0180c14191700c980c011b80010f01039500c21420a03508070b2042009004190300242440c1c1a1446160824940448000071030b1406020921104811910110000d0300e4000042c085041d00c44401d0301740520385d070741c0e20010f081c0d507851 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 636477185 1250 636475935 636475943
    0x301050c1c0b0d110a05100f034d030c07060e0a03080a0e0c030625030e06070f120e010203060f010c0512090a090618060e07270503030f0d18 62
    0xf41c4074100104d40c607001e05950080004042044040d56000050703040c103140b82c0501d001c24502d07074107130034483d4051069880f40140c080c01d20801c100302c5c1405610011160307990b80701d1042104a07105020b061032001a24900610741ea2030742d41d00304004140d01642281e201210118104031070840c0c00c80d0040f842c048490ba15484014140d110545002c01031712500038641150b120300200444669410403415010348015105003424503586071a4a002007401210341007810304045241c20071a5001441c03943c402c000e441c10004848040343e00729680a0105905102d4038101044141d4000c01940194018031040310420700d0060002c006561200d0b451201410a07040031142e00c0000d5814001007999a50040544403800d860b6610781084030825000b9155214a241c100030700c4070254440c20007c0c0a090002640510b441c00006110032143c0015001000541d0060a01c0c000c64101120180c54010166a102c0581140500168100a5498110b41d09103400041c0c4030014403100c1c04400e0700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 636478435 1250 636477185 636477199
    0x230a021c1511070203010912090e07050304060b011b050105060f0406030213050c090604091406060f1801020f01140426030f06010513060e1f09060e030a020301050c1c0b 74
    0x41200c50100500380600c44110b080741c1040040c00581d801c0c81ba681041e4071600c4024585400340c24010090020ae40041550500b040c09105c0001e030001d080c0c980c01644891b0105d0210209401215070851500109200c00107410300d03082040010b410961042d981a210851842c840d038023000160fa0b294803020b0741215040e01c02c3c0d0b40000b070039081198400c440f4802c003803a050018011845950041c0d1000105c01d641d65050880b0401204c2841e0300040100d0b213490420101c02923807101d610071040c0142140803000810451a4000d004211340b007010b8000800c03406045c0c42000d0786425045900b180c4014030071401308031a551202034041d00c4001c1e9242141580d039a0750418405644c0507001905000c820f002070986082c140c110300000e844c140c1c1d14070300d0244d00c100900900c01c02c82c2001d40580d00b000c0d4201b1810310f0340400080200c44c0c41d031501110010303441c40402d0404034140806909035092008202400004c0002464800c5001403504503804130004110700701c89440c4170b41607101c44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 636479685 1250 636478435 636478463
    0xb19050702030a05221e0305010e03030606092422050315160e0915040c02061605130b1b100605030705221d01060f0f12230a021c 57
    0x9020000451000074083c000018a85074a03146c01e400341d200410042c1801803002c1842084428000d1249008a0100650460030082d001900034010424034600507404464071450b0001c120341200320004803101903541e14500c440138031080703205034000300c055401400d0380052203080c0080e94080406094504074541d444500d420a24984540a075404000007941c170807030326940d1120254014107413440316000d42000e4005200503074504607440415500010108180344000107003281d081459850410790310a00162028110100e41e005000c04100c082030301c1408000951071101d07040d824030304803411500e4500601050b203145001d140c4d01504054001c0049007000c0900b0358480b00c2041444017040450101c000445045c0745940000d000407900f42c2d1001002031040001500490b0710301a00c86003842400c0420502c00c0c400d8560080d02e1603811403c1c04a011121a908282440030b005c80320b01000515a0310003180c14244c0c0319002c101401207401d01d0402c42101c0d1742b54030460000d0240703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 636480935 1250 636479685 636479707
    0x2303120a021e03030a230402010e030f0106090c09050907050d020318010207060504030e0a060203030c07031709070305060f27030405060f0d0b0609090408090103090b19050702030a05 80
    0xc0c0014811009500c10500e5a81d151042c01e00c290400038503503001984c4a180800084090342d1011002d08841c07008091071000e00352901c0410780c1d11980a0802181024082c07001c603140c010310a000103403d503e801c002080040180e000000311401980da0007080a480d50100441d58006642500204500f04540304500101d5009103034030441d81a031164441f5030300c02c1c80c1820380e8080e1408888007651001000100b6070404980c041110302a19055009401c105c4040c0d500e10000d0b040c2100d2545c041441420113100f003d10784031071900030419442a091410303d1954800c26404212258081c250006101100080c02d40344107034180030741c600248040c410a0420b20210b84c851040500082002181c2c03511510700603d415040b40c1e040e250348681011030142200c03c241c04441c4a15400c00c40c40d1025a204183c0787d030016080007041c1e80d9103c600c40144c3c024079007004001d0115615408005205100c40800140c107043c603801800703070769101c044c102c0c1c480c407800317080c00d0118078240b2540b0603035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 636482185 1250 636480935 636480937
    0xa210303090206090604031505010b0a090303180b040b0301032f090601021c09060e0a0602031b03120703020703030e0703081903020412240b150c1009060501230312 72
    0x146001600451130504080042a05130b44a50810340d03989030000152241d210b414482c0302c2c0184422084642040c01c0e105000300305028074030002d42005884000d103030441c004070a07420700030080030713110b541d4496407604c01e008907420911080d170780b0400c0098000843c501801101e00b1540051010300c20341c40c0720b5010480907440241c0450304510411582c1120b007003400604981042440d05e07481282450820b005003030b1240c1004032800ba1719101c0301040500d80020941c0c00740c2c0485000550380018010440380396000715919044140e003110300348501c80b5015401403901c80d01030b65042c080c4502002c1190381e0b4019500c401008403808100c521056030a091a90051a82600c0c01500e0107654642500c50354184080984031220f24500207641400200e0b0b13a01840c0480c0481070005040400000e008103000c2400b04800705400034800200043c240600e80152400309010003210040d400d158008040074001c400e481107035660328540b079080148405298400080090004000120100d082 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 636483435 1250 636482185 636482201
    0xa090b030606060703030b131a0d0c0e06060705120a1b0c030803070302040e10050420160809030d03140a0902090c091c1a07080603030915270a210303 66
    0x201075072041c410fa41fa5036162602e01ea400e011300c1c40030606808010540030310400d501c0055110311090035480f0006001c02a0301812111800851103181e52014040f9150b40324660000380f490080b10400e608002050024001c0500b542d500e0032460400191243c000307198500001c1c1040107821402c00c0010040002075500544c5444c015050554840381c1000d8010192022150700320310010500590401e8030584501e0510100f96400c07206014000b02054480c821039241e584655404900520851004071100b03154050200d81100a20600080041c41012110488821700d0408902003403080d006008040360010300b803c05540300c01d84024010b50241e45c501d90001c03d40341410b1410072007107000c05107280c0540c4e00d60b4591032103111044860318005140c0f40500c1100d80c00d00c64991000019035500b01d80a075004107626100000e000706602404405803500240198800c01e008442a601a80c075001510980c0b0034540341c611501c81c1854286068595980c0101c0c5500400c0c800c0d004680 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 636484685 1250 636483435 636483437
    0x1403130606150206090d050415080403140a050309010f02040f0e04020307090504080d0b1503040204091119061202460c11012309010207230a090b030606060703 70
    0x801d079664408407111800a6405800540c000508002d000e0200f4004012200464980245007600f030902403000300318114448010412000300040400d4007409402c503c458850340186d0b01e4030001c640041140c0c0c01107030384104135400d2410041c03a103800d0b802502d0664244a00f1003a4290030041e00e0300004070010400c0e60315118049000070784517034070b10903540070324003d94800340d0381c4440c07154400039505903042030b9000c0c0340140c1072407404043c20000d60b0f400ca40c0c102e5010174400c03040c1c00c00355a0200c4841200d680414800b1300315100d000350b02d2075202151116105e0801000c1507a020703a00300d002c1d00751140c640794521443d800e80d000c4000c03d000c1400b04600c0041c0040003040c61034840d510f841082c0707000481d200305103040911081c12500e1103003403000d28045442d01c2020619480445650040d864160030105400740641e009120041c06002c00c40d502943c40307452040b8100c006000e0301034050241b04180c0010808405a0003114503d1201400600c21901c9010502080b1307409400150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 636485935 1250 636484685 636484691
    0x161809090318151d102303060a030b0702010207050609060106121808071b0306091103010c0c080c0a0203060c120601020f03040608100b0d09030e040b18071107061106060114031306 79
    0xd61684c1c5e1400320002102c1c1655801114440344582041c1c00002c441030900d205070600412001d035659040700700a40364008040c03001a1201e50742070f4068010f900006242d40100000c201c548003001231482c1c100ca00c17566030501040442c292000403140a441c0302d030140c1d12404010f1000c42c80c4540203106080c40791040045001201d18252b0010406070012600640c40d10080024003403d0902540c680000310000c002c40d48011401410728040488000c20003440403c450742440414003168002a070040d054030031918203890003007030944c08146416100d142c0200416219480019a00c450a84e03482c001c514043c140003051303e100c08003c01d20400f0001c01e0901043c442d00c800040c1c0072100752044082062981e07481d0242c00000343c001c0403030040385408080401c1c1d0703845121070300e10282e00079011102900c440d40e04807114243d450030360034035205864000540c56440802002034000540c00d94800b0346075480115140321400b642c04032a0301080c400b064900400c03d50513061070344151000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 636487185 1250 636485935 636485987
    0x90506161d240301090618051909050309180f090705060d05040c24020c0306100506030a0609050903040303080106090b0a080a0b0a060201140a05040b16180909031815 73
    0x38906a40240c00003c0c2c440c1d01c60900b0000c100004090510003003107c40c041c0001d00d407800281c1e440e820805408950191a000301d002403020900c1104d4018030098580b00e4448003086c0d8128019106481700c5041448070070001d4011400480c10b50140e0f14000c00080c0b40c51601e8402d5000780201a1050b5030b51618400c00151010340ea120b41d84d85403441c3d5030b0b81c1d0201c4041c07100c003a041c290b0b4294214081d401c00c0d01000400005000c0f403c1c26070384100d8401d901c903110302c2c0b1040c0c010811500b0807038080346401d050003042c01c40003000e07104480c0b007640c0789501a0f03260301e01100c2080d01881501c10280e010b1058014490007244407580c802100307400015000010350001e40c940d2455801640541d54030010140c0803510904032580c0031131415400e1006082507912007d140c24000d0101400e601c0203a070000000740314316941031000030b8400300024200d841e51001d100030500d50750110049404c0c1c0042c0007074156603000340801c888034401480c810200125007074803035001210740603880740589004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 636488435 1250 636487185 636487249
    0x11112091009091515030506010f0c03050d05010f05031b0310050a09020d0c080d05090d2d080a03140712110918091e10091401090506161d 61
    0x2480e80c01141c0d07400d1400c401032070801404404407590040031301b014109410400f00741d230480a0402c03402046e2401d80591516418101c5107401501c0c0c40301e000c64180400051480442100102a00d40031420744908c0c0e1000c0b24004020100c4030101a09500700c00401c0d96000c035180d02c510340c4402c0c00d14000c210700d500e99000800640a10b0001c0f61000c00c610018032051700108540ac1c155001c6040045c42c0c2604140000ca10b00301c0400c0061030a00455003511000c54400041200c20244c2c04c60021142500c1c81e102c207aa4021400002c00a450403400002820450011500036101511050034242e203d00046028000d801d21280b1824010045040c0e651602e070341c0e2101c000700c90008064a424000740702424034004801490b40c48000c200c03021600d0783d021450180c04000100e000442403a1441c011072120b283c4400d54019501e440c50180500c04040b0308544070300407a01d10300c0c0f00c200901c035040e00c040c2c8007401600701d00c20040c41c120b109401c04403c90200b00008840d03006502c0301c4c410b8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 636489685 1250 636488435 636488441
    0x70b18040e0a0510110f1b060105042c03040b070804030209070801120f02031f0207020a050f06040b34020907090b0a03110c01050420032806060e011401111209100909 73
    0x1428800307030b0507c0c0140c0c1843c0c0e201409014058241160140140903880078980b003508011507800817000c03086018140e2030002041154000c0000c00811500d442950600c0c4501d50490312013640103102610000340c0e030790710806809040ea01c0b40c000b0300b03000d030004d5141c007000c000310340c10b04a130140b0507140a841c0301c800c0c030912004640766110001d6a50f05030b51050086007607130faa00c07560180c6e006000100e0203907110740036542642d130720518280e120300c984001e0007426040e1002080d446a9060380001b0221031480205010030f00a0303c2448103604d0720701049130074070014402e40000c418244100f00d80c4511a411040c5424500440f4034100640442200e003114026070701214111450541102500c1050004107441c6074102c01034100300c503040704032642000707901813804401100b1184c200204034203a40941c019281050024516603120a050100d03004100c400601140d85040050001c1c440000ca1048ca440303000210741c2800103503028040c4400981104ca0284240315070041015001e40c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 636490935 1250 636489685 636489697
    0x2060301180f0212060603070207030c0306052e051e0a09060303020708010203040b0f061206070e0a0f030203070302010e06070f0807020906040e070303050309070b18040e0a0510110f 80
    0x4180304800340c0c03100c0603010450b28603005161040b4014048031040500a11300554410700503510155243d48a0718100c0c10110701303800c0200300d4415040044142b04003a400f1911400b105003055418141d15a00c510252502c0c081116401c10102c40a001c9030800c000b030003e4010301c64150ba485040307075000141000300b00d60400e0810076a1110100103155040040400405c1800001c5103141070946038001c0c1640c2c014140b0240c100300c0c001140d00740c0c5900741010041280401941c119080c030060051100007010729a030f1094400c06004034000d20f500290500b02d950090080900c1c1d4034550041d00c040b5046080c069210740c050021001082d13844280b9000c0900c14881c07995030f0303071a910400020031070140034140510300e03010341064900710008686c8240c070f406007000d03502c1c1c0d0f42c2c07900d80c4e500c0d14059400084241703401045040f0303500121841494030340e5040380e040c0714012102c5540e503038482512001400c00c0d48000448801c14041d81d025518400000d0003040c82d089089901d010164801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 636492185 1250 636490935 636490949
    0x414011d0a02030c061305040c0c0f120908070e010e070207081002071203050606030a1e0c03150b072f1f0306050f28030609080d0614101b02060301 65
    0x1c403500c41180340c18030484400d202c0c2140c50a051206450760040310303243e41d00515016542d07a05001c01640d0050702a011200c3d8800f0400022201a2500740d0f80c666403040e542d4081400b10f203010540d28030118032442503415030180e4040320303032800e03c035004000005010a030960040803008100080c1c20b11440120510041001d03a4030011071034840301c031401911010040501c6c1c0028455566101400c494102d1f8106802040c03c012011045c5c12004880c802c20010700e01c0d24051000c801c0d0950070411480c1d1070104000d10642e0745403c1100c3d0b80c813442900800b204c0f0000b028031400f20b80000c00c40050b00f20716508022001c5007502290100300060711007140c020b24071320b40040e2280c1c10301800c4041c290903100d05803180190030206881030107405903843c0c000f60004444180701c890324180002140c1218060140c0003031424114402d61001000d00c103070908152001c9494149201400c1b8240d00160801508601100048030100c9a9003c0c0580102e603042c08900980c0c5c0b180e018501070092 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 636493435 1250 636492185 636492193
    0x807050a050705061e070501062d0b03040201020a23030307080f0702070e070c02060702030d08040b1003030905011209050d02070602010b030f0601030318030510090221060414011d 79
    0x51410064a0310b44030b6800a0300c10351041001c1912009245104102d003001400c1c6152500ca041c80c109016040c2034101210b071a00000000b24040290400c881c0c1c0541e0580f84200d2454949465040c1ca120880b000390160b408400c46100040300603800441d46410300c0102560f0404d45e8490600310b500a81c0c00c480012011010300c284100a4035003240c10941c180000c0c10503500c2c04c80c0b45007500d08020a50400c1c0110000c0410654951608641c003d681c01410340317110a044190107440080d080d03a09036038400e000030000300303401103032107480059a4158480f00744e1949041c8c01110070500180d070180c00700f500c65a0100008404110880754035070190003800a09042100090844400000061003907124810110724034801052250549405191a00c244054114481104100c9600040052207a5060300c030317071a055a800710700114821a0f04908900c0c021800a410400144182e00d0941100c404030380041c024102c1c034803140348041c001081c9017480411030031003e0503a298100a0341c00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 636494685 1250 636493435 636493453
    0xa09020109060509130c020708010207080a18030b040f1a1e0709140f040e0d0c03090e0105010503180705100c0203061b0d02091306060509030c0301050601170a09080705 74
    0x28004222402400c030b00c3c40c0c00350800700b41d0300c001076100c041300080050315682c0341e8001c085180700f8001003000e41400d10082d540d5844901d000c0c64180d10602214002466002110001d0343e03110346010122030b0071410210301030301d82d902c841259606c400c9040b0740005440309019003c600203806a4402d007070000c903911031092a0b01608252000040c071003010001d07081d20500c600c0045030b00e003940840313054950300c01c141101004035008054601000700710384616082024202d610402d02401c2c02c0c4a0703501d40c0d0340d09035100c0c0b8082c801d030028041c441c0815401c1c4001110312001c208080c8080c0c4000341244d07940c650f6035000c140207000701100d440c0010186010202541020802c194114902c440d2084214a201092041c140100702104010310703000603610440b81d4036801448a0a8045c0303004000301d036521080901590b2145403600c0c042d00805504042514043c407a580c820901a1900418041c428840108904d4002e00c42888142d41d001300e100400c1c083d8010b0f0602900c40e070000d0030420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 636495935 1250 636494685 636494687
    0x7020c0402090102071a1e0a020f1609050619060201021b0f0a12020709020d0603021c0209010504180507030302060f01230d141b100507021806180a090201 68
    0x1025022064010390040003000c000b668001143c0d0100d41c102982021210401000e01c0c91500c01d02151382104055404003040114409004142d0a12140c00302d440e0f102101521545420a410001c140030411417820480c45080741c0119600070f0000b025440c1503029004402400c2d55140c22210041c2e5011070380c1c0c0e040c504009040c0c00c000040c980200101c098800300d180d6149a404070041010410024030301c1140e0081004a02401030010250740b50000c222110700101910b1009030301ca90040034611180c00e4141c21110040e80e0007520316005a801c01041c0000703040c0c500780d906156055100b822002c0350041c403182d0080c601c25400b501880c1004841c0c4d480724141a04001c440c80d00e0703a01c502c54500841400c5c0b0208000130b540310724400005080040038100c40c14104105c2d4001c00300c7c100c50004d026000c405880710b0444050000d8010010119200d006507a4001c0d044101001d10461a000354010701e640b040008240380c450041a1000ba41c0b400000e032400703202c140e12744440d08215 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 636497185 1250 636495935 636495943
    0x90a03050d0b1324051e15070b0415090507050913080d0606140c0c01031508150901111204080721031401050d08070b100f1d13080708250b0702 63
    0x40003d0301c401c0d10700c03135040400240d031031b00320b1a5442a000c9001b045550044d15140a000d01c440e07040402c441d140e0026041110800404440855058108424080001043e846004500340e0890020040346041000744880544040d100901011243c0c00001c000340e0500020f0902c0c2c418103002207400ea00c0d08030060084035042e981d014038200300340119900c580c40003035038494200d024a808901070079003042c003a115500e1074200400c54040c501c030030055034030011034507802420f82c03400030072040c03000c001c1c5500680580750680e00b45050303020104002c102c04002400d1243c5c02542d40c00b5080940d08910b0600030b80e1811901c0100340c80f404009461007007201c05900405c0c00752144106580c0783e5031005118891440d00803c0f104100d40821150180112401c0c060901c2005141c01d49840d40c10b180002c0003c031280718000300401c000542a030841107003000c06142d2240700241444101c3e902c00c2101d8001d001c2e030f00040c0c08018100e10420301400070f810300b51809240350b4089400c002d0802410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 636498435 1250 636497185 636497231
    0xc12050f0609121213151a0a08071205010e0105010f030309050405040201050708070c0807081005063c190303020f06010b030a090302100c0302090108010806090a03050d0b13 76
    0x82500304070100d4403d004144102c44c0c60000c1c100411469035591002e5441c80c0103207410103400718000a1041401801d56408490a45003525404c1096074034141008060502400f8240d925001500c0810450b0540c020a00030b0074440c0b1700129000280d01100c40c06c40780309034003102c2050030812040050540080703258001d400203507401d20041c031341500007900c180700b03040008280e4040081e40300c0a110710030003d40049d000c0107090350700d03681d40c9400e0140d0314000085401c00141ca810040707116442d11100707824810b6101d0600ca2116080248030240007482400100c260484040400495aa407480386240c445821003034042c1e070344d08504000386082483c425018440e40000014045d88a001050301e51284c1104404121072100e0303d030880c24603404e940d41460141c1801c0f038204140c0c1d01f540103841d04c3c140070390b9004034680c0d84e09005540c03614182c803981000d8120b06480c40c0032034454001400440080310b80401c070f906a00c0c0202e540c0388402260b00795450364501ca40d040c2d85851803581d000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 636499685 1250 636498435 636498451
    0x7080d18110f030102071506180207030912030c050105040507061214010b07020303040f0b0310140901180608060c030f07021c05030417162609041518050a1b1b0c12050f06 75
    0x10030401034cd500908084024003a810030844420302c080d0030107100c2c0305540340e071681c0400280514100f034501169103051a000e42d401083c0c40c98900c5010038058800d116030b122000c40410001e034a0419000c0f140e0340b010000307a0b0540400c10010a000005003801c00c0102140d111141d968986010401005109500326442c01e54a0580440c0960f41d4941814151071100c06044088541c049185000348a81e91101c030310380c0510307810040b4410752803002e035214910b0750010b80724940c2c81020881e200ca031280310003184030180c102d0321a24184960007441d030007403003440d940c40d14040e0f00113071240503000000b02e440b407002240c2e40c4908000071b441400c030f10001c0900000720103442c0103800803010b00480c02c0743c500403943e030416030780c201c03a1680500004182d945415007160341211009800380070304a4108151030b080841844241c01c20203500d0031000d200e640d4800b145018544000c1c1c8100e9070b21403c0e2048000b00300080350a201d441d45010b00148200000c0807a00303d0040c0c020300785040240610 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 636500935 1250 636499685 636499687
    0xc0204050f06090f0c1b011b18031103070b0309010c030605030f0d11070510170705041a0a3005060901050901031202010e0307080d18110f0301020715061802 69
    0x8680c075014000da13041900e0286107145030341c1d0620b400c110341c003501b03105a80c0c0c50302c0010000d4400308194020205401c0118503850440c2032090290740720400281180842038600f44108081407250b61103aa10110090a44058640d24a00401c03540c01c1681c000300c003655035101e18070390346c3d8151282c6001000c00f9006009080b400018240e02e417280702c0145024030820340c3c07800003c1d0000340182d80280c40d00516030b01d62080106001800064030403182c5940184e8200880d03480c0b401001658110ba0083e03103040078040d6020b03064102c603040340340702c0c2c4140000c040c2081d400c801c42c14403240880e4204100c044403c03510304c40c201c0c10345002800b01d50048030b24500502c030701d844181400d0305403038120342e5001403d10b05640881c010611060002c0c803a0001003044401c2000880003050102c100000500160155600c4001c045518100040c0141c0c14015040c61a040200b00720f111740304001c0005060611035111340402e0b20400e8403101d10300c2d582d1081401941c140680f11400669043c0c2d0031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 636502185 1250 636500935 636500941
    0x40c200604030e0f0f0a0308030717060a0b0d02070c0b09040b0406050609010302031b03010b070b0702060601020c120703020402030a060512060c07170906131a070302030702041a030d0c0204050f 85
    0x40c1021049001e45409504044811001c0361034429038080e8011011b440441d00555030305000c0e502c0e400944000d400698011030307501c80f00030302c01c3e01c00740580f038000c0064a03050b2500303251030341035031192060740f06032034082c03100e400030820344840c1d04000d145003127100b540c4070000003c0201716002c401001e88103d103407150030301494640005a80c5c2c5100c007030a0069981d141e5040c810701e075100e000d03000a4500000000442d007000c0b590080c00b41c0d50710402c1084100e844105050707171034032000c407100d900590100c0c811118628200e601d0031040c617014425a009152650040303402e0381d00407607401284507200c05041005041010320a480d035003140c1c000d40070702d0500028440c000d2050040142404030980c000004026030402105c0b0388081c02410741755950710002500310043d42c42c1c401d40080c01c01c0b915031215404496400c82c0c4159a050340910b01d4420b080d420080200178810350180506a6032850854035181040902c0107081c541d11010900859481000700f070700e0b0002d0038008015240e000b4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 636503435 1250 636502185 636502187
    0x201200601140a030807110301060810020a022e0903051b071712040311041112040303050c3405070303021c090b0403080a020c0303041211040c02060601120b040c20060403 75
    0x151a1207c0d840003031030007001400310000303000d4841d0f600140c18501502e00e44000b0220503a0040c80f2180480d02904c00c503044448441e07074181040365640c005282c03481806005082540d0050341e0451080c00c102c2d04125403900031035403900300101044c0700f940c04064144a43c401c0310119419a032006801480480d43c4201d40c0c0c84140640d11004140790400080c0151950341c6400c491010070018140540311803028146a128003026101039003c1703440c1c070707010810300b4000208641065400d0301c8000e000c0d100031864503030310780a17100000c8980c0d403540c485000000e000340f01788001580281e00501d000346403140304030080c4a604210106014801d00d00b08400110901036904032a040b01c0001d80b030700000c000590400590540d45075150000203804600f070341580c042da003043c0f80100003003071401030b4090920003294084004403000d40e00501c0081c5180d03100d43d8200003414105400400c03181c017040081400c0ea1184640600032070304c0540d407658114001a80b90550782035440040401d17080c1520 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 636504685 1250 636503435 636503437
    0x11070e06010519030204090f02030610080f0601050a11060c0a12060501020d030e160f0810050c12040203100903050a1e170606040e0c070b0907031205070201200601140a0308 76
    0x820498200581100300e6103c50080c1e06407001003401002c1070142d000e48581400080d40200e8000e8072481329003441441c0f41c2d208100c0036114000007208503005465003030042d60203802082100c02041008020000b21b80003d00815004240c54410f181d1988511180642454880419254114074082c41040303103aa00188024120400382000600ca605011080d0300b030102c8401c3d806050010b4001c000360b83d02140700c0403003c40c0c20310000c0d1081d40d2a40980030043d0345065030020044101800641030103140681103940040c8020300300c3e07007080d407c11046425200c9101040e80480c3c0007040c00000e03213420000071004080d490b0206034078807501b044098030000c1b070b0043c51048184003c001a00715211001140c0c0542044062100703185003500309080590312418007101c1c00490000450308910300055843d0a4a902800407001c29124907801c40d00f9400c001e00c1607042003640008104c1d96151480109000c0c0c0f132002c042c013039079030504400d8070201c1100540e850252044a03001c0000c240004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 636505935 1250 636504685 636504697
    0x30807020906010f082410170c040302090f072003190c02090415110f030103170f03011a120906040c0e163903030e0a02010c020409030201150611070e060105 69
    0x40c5a01034983c46e070350b8600341901e104100040c2c2149002c2410900280c1003a0600301400740d02110034640d5031103410320205c41c0120b00c8025004642c07040440d00324041108015131260151404c0ca00e01505a03419030071000d00310700c4c68040ca80000804090380514841c02078038030000c0c1e041000e0807543d81d0b030120314500d00090018010081074248800b445020340c00089001982600030b80e01c0d5003152540b00380c1d9074800e2000720b03101d0613517110881520310900181c45099078403c500d2400c6a1a084980346400c60200d1101982c40041241c0e00c2c0c0b00c0d0509034503d0003607039030b1001042245041e182001d01c41030311303800038108075102d4000c200144505951110b42d004040c0341040c0600e80d041405a080d680315108240c11400c8113961554041c0c90040d410801406907a09000503051041e109484510b000d81c003038001b41e4181101000340c1050341000c000f4520910000490004541e03000d035600ca20350300201c00081c0c80000002802a041022038082d003404800c02c50b407414040b0019165200f05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 636507185 1250 636505935 636505951
    0xf0b093d0206040b24060d0f050112020a0509070909060e070206130c060c02030c091602101e0915060b0c0c0a1202090903120a0207150b031b06090a030807020906010f08 74
    0x31050130030707105c941c6140044a850040c20f00c64840c0c5074922904080d10102c41d565074010328001c00007134505c6401c500030612b03a80150160182c0d90030a401c0c42030b80c9000a050400303204041c3e02c0019405014410300e402003011440359682c3e41426100203040c008081d080c20707000c1400e40c03020b4000c07400c409146021a451030038070240d0010039101081c1441e045161155000103003c04120015030000140c039460341d020342c2540c1d80603e689101004648642c0d4206401380400f032006502c10820364040d100260243d00c000c040b0002003c0004140c440640041d6264200800c4d64104014204846010316908070740030302c0143d00b0032600499000680b00064030444480c00458107038070003801201d04801c05a204c20005140c0002980c02030345c000785040303075801c5d10301d05101030075001c6115003071400e1802030290039414081a0804022018454001da01ca80100610082c0d0b6036840300d150000c40c03041d0056502e91405d07004004111100501d0641403081008042142d03d80c40182c9a80c01462 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 636508435 1250 636507185 636507211
    0xc0406231908031209150c071707060207031101060b0418050402220c021221041e03080103021c170f04030b040312050108070f0b093d0206040b 63
    0x803110070102846140d008204a000c0014640e13007041c8010641c0d0312820000c42269541e501040042c0c0148100f01d40085200c0e8090082c640004c11094810f165112901080ca062203035075200e142c00c070ba2050303034110041414000e0115408000380107002c0100318115480b81014541007204c5e003000075074403085034241e9441000504550346c032401034203000300d03d5180b401c22046109203903000740600e4032076001500c9a0901523588452000031254000701d044100c9000301400642c5643d46a4090700880d840d0320400e00c2a8902a0341e00d150342d407d103000b03a4074502903524500502041c0d10740000d82c049032014644030384d4040340c0303903245020b00b030b02064104603a6242084c140c4005401203070030062000c0300a074180420b05034130051a10074142c095200700116641c40c0622680d44d2040e204660f030300c218581013040104000f40260491400181049c62080310909416506414290b21036180709094818698101000e8103140346007a042e0004158504240d100c523085800b001740781900c0444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 636509685 1250 636508435 636508459
    0xc100b0a06030f06170303014b0509070e04060f030804030b04110315040b060108012301050d0203010e0106021213090e010b090117010b010c0f0308100e01080c040623 73
    0x1140e40004000c11a030035003070304c0c01c10017003050700c0e200d600c2071040b02035000b00b2801c0c140304081c65410b6513000103003401c040c8061000450101f504081001510055407001100c005155110210104d218001d150740c0c02404096510801c404c880305a0019540c052600b4000d000080d45101203d00362038002004140c11341c0c3d2858078000a00000101c00e0309401080c41e008510501e00c01224000c0d8415612222150340e04801120100d00910401400c5102c032205440443c44043d0710f55400141071416500d00784006c449141603038030a9000c11854283d01004101003a418003c1108407140f4641030f5282403101e6001001d0303c0221b0052905896684100d00b048101c02d42c05801d41c3c0602034102c1005603903900b80e2000350f141c0c0680e0962554241000e50b030456104020300000c1c6c0b03a00a055041184503a01e04a810010040007014134007030f10080410f11103d6408a14002c200000040254490714018001596070507840b9040201c81c0c150400c5082a201c0b5554200120685681030307450 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 636510791 1106 636509685 636509711
    0x80f0c0f0106080d260c03060301023105090f06060f0706150e01050411030a0b120609033601031e0c090f05010c15050703060b0a02030c100b0a0603 65
    0x41d810000f82c103854610003448d0080800f83c0014200391131250381411401c0743c51001c0560b400310310b0b801e51801c0e4010b0820000350000b0b980c00080b07030402c90340c0c00c01079220103001180300e9807010a0f5625101828020740f0394850b0008018010003d141e41883c0c9040801d0141c0030158000c0400440c2500340b50040883c108100c8200030325503551035021b40010034038010001d512081034109000244020440d11740110928030280d691820100c000f5419140d510491a141d818811400410568503d0032410164028200891012500900c44180122800703003143c05a10f060200400d0303540c01011f14066500310340d4000d09140d115801911010140301c002040c00ba911032104c2d003002d00d0754101c0d5401180a0401090858072a0220305040e004403003802d0040e0f00c0881e00000381c00041120f140e2030100210108003211101300030441601450003040103068449071940100 = true := by decide +kernel

theorem cover : BRFrame.Cov 636330935 636510791 := by
  have h0 := BRFrame.cov_init 636330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 636330935 ≤ n) (h2 : n < 636510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
