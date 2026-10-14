-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3636
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:14:48.465144+00:00
-- url     : https://prove2.me/submissions/07b3d2e3-7426-41aa-959b-b2d06b3f7626

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 653776978 ≤ n < 653956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 653778228 1250 653776978 653777009
    0x603150e07030203060a120302070501030605011701030213242607060305072709050a0c05040b070f0b1015050412024b06161122090303060f 62
    0x1c0460180d000a0700950344100000d000044224031000d120154610a8010702440e40c40d000002d4115030305640018140001d45c2c21540702c44006510032030544c0d604031200c410f041d181c500340c90001c01920200c6000c0107a03003d5206941c0103c00362001c100ca081070506046250022141d9880c020183c04086880d4002042803017154007030381103e540b1802626040b00c2d003010b103a0f08440c07c0701d4030780e8804100d445c007040280b2a003800380c002c04cc1d21100001c0103001020000e03c00501c184614841d4ac018560089100d034208440c420302e50134555004145400c40e810700e1112242c034011a4812f1285031450b4450400b040b5006005440444915101b41c2e4003000c02c0341c003848105800c2c04100030840348104c4082003e0480300903101c0e4210b00c203861900050050840c510031008000d0342061003680c082c0031007000002600c8000042e181c0c0700755003160303900c9490007103806039012203a18a003401e180e0b40650080c03c5541d105010307040c0242d60611010b50344105092000d0701d980a8100300c03424844 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 653779478 1250 653778228 653778241
    0x309030304150216180608011a0409021c121205070c0b100b0309030c0c0904020a12080c0304060329010e1005090a0801020702090a14060405131b0603150e 68
    0x12080300480c40b09005840c0c00400f00c6600d10000d20054200346509404444440709480b040e01c00d26000d81074280080000035140c6d4a1201d080b250740c200c040c404c0352181504400c648400c010800441e04034081c1503030f810000e1502d80307210b15a202c6224001081130050403006c2c100360007001e00504541d2600d0001e900c060315211142c201c020011440c076101d60a0024000184800841c804c181c1440919115603c1e80c1005080600c503260b0240b0502d0203805000140e650445800100c0d0b155242c1c1c0d80f83c00105181001090048880324030070f50001050000c2d44075016002980340c0584d04600c000f80c4041c0c50000040041c41c5c81c1040d0005181940c10126400d000c0b508404181c003e062950a00c01e0040000d94541c0060300003101694002c14030004500303010042c03036003244044c04c05105800c42c002d07c491750701071b0040889108a8030385000c25808030386444600f00e402d0f0451806c01c0a007042074111800641144030b2040024030b0b040342d05c001d0003142e01184040d20001d40e4944c401c1c0c0c83c3c5c0c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 653780728 1250 653779478 653779499
    0x2303010909020d02031005100e090709020705070b13030605010506070b07050f0d05090c010329060f0d151a0705061f170d0305220204050415020d1a030309030304 71
    0x1501240c00060b005001c00159170104074080da0900b9050020820780341c01604154032880075401038159240300790a0081010f00491a0810303070703200c48001602d510b02401d20314130b030008941c411602d10070001103e01000d5120030302a010742e8002c40c001d0141e40d1360740d428400c2d0303031040c0c45e400741185100b000840c803d075120300300500b00d190f1408001b500340440d40c2d00c0301c0c08990047e5003c100342d60005c82e200c0841e582500071500400840514041410354400c035a608200915900c03500c100e8000407084c1710b001a10098030001d8001e8002000200c800d80700c1c2c070360541d40314081e4401c0762509110703041021602c502119180e9520601626141c0c60b06481d10002074001c104030000b5810148012071031305003419001d108112031a00518643c0354841340a0704444020b0800780281c0346180402030500890201e078102e469050300c000426944604011f1005070b40c00c40b080d021640005058070b6280c1098100801211200c8480039500007810105a03492042031040c94042c0c009000402103032101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 653781978 1250 653780728 653780741
    0x71b0f14090c16030c210903060f0501120b0903070c090902011d060a050306040207120c030e030d05030f04050705030106090906060f050117070c120908160506030114010c0606080c0123030109 84
    0x24400c410780c025007080581d0280816444030b60000b00400d47c1001401200d02070098401c04c0c01c0000c1000d5418140d1042c0d44400000e07014201c2d002c070710081905030704208102c90a05400149000750030f0388800e52800030300002e40040c0e0006001d0803404000040c946003001a206000b45401e14210301d0520517101908000d152680c841d41c01d0081d06c000c200c9100594020a405540304021b2550b185005048030441d101150b001b548080091081c440e00031040340d07000a4400580c0701e6070303565443c02c1440c00303400f0340100d83c26500b009000202c11b15241c02c0314001c40c0c0320344000e201061300c0c1e012802215405200e018001410390604c401440e03e9100500d40001d82c03403412603e00d0549032615105003c507100e030302d00050344415080040c01400d000380c84102d201424014086880e18000403160300040c050141c0b0090002d0f0030703200c81d80c021003101006550000060000b01d40c0c4902c40c607203561040a9150114a40011080e03003909090b0100d5818012010f0403800c590a02030348400078446d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 653783228 1250 653781978 653781983
    0x32309040b0607050303040c030c090203010f17030c07032303030f06010c08121005120c03120c070e090a0302010e030712030216080d0606030e0a020105071b0f14090c16030c 76
    0x400300312483c08268284000c2d84901d000d511010a81c51842c40c10701411505548040710091051005100387c00d51000004111a55100d103040c1440c20920300a084d8400c544006020744501c1d9400420000200f842911100d1b031017901d028600e1340081603a4503032100300c1e51206450176520004071950702030442c00d0f5070356014900c8039082005000c0703079054082007070b6003043c0c590282c964104641e1508a508120107480d4001512440c9843d4000c40c2d65800042100308030200301103035001a43c2c2d410440c02009000c180c8046100741801400c803500c0303000b03280d01540103508041000b40d840e100002100d8880790b000c51420401c288206003100290000050340700d051601291840100d81010042d0856901e1060300040791071400002038200d80c0740c04000499500b001c07070740f040941e070468281c1c8c0b580b6400802403a440039405034948003542c1ea94002503541404820b01003001c040030f407202505804103880e003e03c41d44030301d6807407000c50040c00100e501003003070000c2a800291054004461661 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 653784478 1250 653783228 653783239
    0x1107032604090e0c040b030334030e0a0801151e0b041403011a0d0204050c041a0a140405220902040204080f0111040302060306120c0301090f032309040b 67
    0x354032240e44200d81d000d54400e0761000d454214080d2100c6090011108941007100e040114540b105d01103902c0780900010301d44c2401c00304045a041190000403410340d128030700700107005d03c5003074507010b4805c0064034200c40c000e4030001804a01e0140500c00c502458094103840b448503460903054100f5100c0c1200c2e811101c4015200010704141004041d0014241b000d080405c110f46d41401e05003110340c1442420b14402c00a05146e5113915100e55901c08990107031000b1407180e4488880e03240c03c0c451a40300c00106100c3c000d29412805840c00079100c034400c143e480ca0400c403540403126640d8080c03070280941c818000f841139122a042c998222000000546c004183c00390355400050898000c1d503c0851550020140c5280b060002e10520308103103061400310f8141415600411003e000043c4a280241c292540003100510704110266079841e00500a1105100364038000315003480f0765004801081c0151082c0c1c00660301c42801c80c101e410000c000f5400d2115010802000c1d041410724a42c200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 653785728 1250 653784478 653784533
    0xc051e070f11040e07060f1d030607080f0c0403080d2304060204080c0a2607030f050d080a0e1c0513080318011404260f0601090507110703 61
    0x80d000c21800381c007890241c200c41c8075550601d0240403d45000807004203050704502018460030350000d03103949007060603140000c1c220008a401b808604150307601164144591000c021240340e10000d058400d240510100c0c1c5962201e8036400c681d4000c07404020048841840005aa80c07850344c01111041c01c240100da8201c400e584043c01c0001c02910306a845c0e0b070300040d052080d400b0070840300c0c82c0803000343c42070b541c03003481d01d5900d80d800841c5080c410341d8140f5114808152003c10454413001c0e5400c090410321405207407034529070303500381c0d8149800072079041000180d001c5c07041c0c4240c074801c20800001d8902d1482212810310301d03944008840d02405070902c4047c07030740d031207002d00303040035042c1e01c001103544006c0030500041701180440540c2c10460f40b07141386085a0080d0080e141158140c840100c4034000490001070706c80b03d8441c403020144240d005009900d00700260090403210312030340401c250745a042d41100d030902c0d1140000026800407000708005921340740318801100c98a001005032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 653786978 1250 653785728 653785733
    0x13141507031d090412080612060103140f060a230601051930060512030a1b02041803080a0b0d020105030406020d02120117070f290f13090c051e07 64
    0x2803d050b6400d0717440c805411090000c040d048641d003a00071004075109104d007045451401d661b6201404010002c41e4103001c0032020401c01c1207600b412118400541e800b91130300b200b450b4010002d4002d0311031600d4080359490001190028854090070381a5105803602e0341c0c0f81050076802d1101071001041000f440540052865006c1108401c0308441d034201d41c41b4030a41d85c80b82d0030f548071500500d00c200c02c4070504111042000085a482d019241400c90a51100c004800307840d03594001d002e90085d0070007000401e60040401d070ba00748140b080d00c3d000320340d4a801c0005000c5990940c481c3c2c3c0c01c00001c1002001560190003c3c5601500c00d460142c81c2c00c00b0945014180c0c0c0001d0380e0860742c0440318006000c01401e000c00306441241a1004018081c9042c2d8016600f030f0241c4911040050854441ea0300c0000c8000c20540a80100005554038050b107201403c0540c40380a20f00d988944900340860402c17000e005400c40e0325100d0751210708090070302e0810300b00d000f10b1801107800c0002c10000a0b00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 653788228 1250 653786978 653786989
    0x30b06031f09110409060803040509040210031b080a050a1a0d0c031e0201120c020c1507021f0906141812011b0f0f09180204090213141507031d 63
    0x1400714000f084a0300c41e40f0700301400003514440c1c3c2090145400034407083c05103403140300103543d2040d01150400120012946c1c254010709641e080c0032082c5030001c00940b095500301000f41d001d22003e10041090b9500c0c4c4d41c68000320b400960042241e180c101808007800c0c600329002d4514036003d0400140103035502d5a8204120384a24003800000292002a9095607003200c030309030403401070f0b540500010041c050000c1d03c8105c00c444941c401d07022030200f030034910155400c0c1c3d40790b1a40501000e00d03451600d12100781c50b0b280590401c001440c3c0080101358144903241281059161284a904021180501c4045580d111029a40224080b00300c0070b610003090080e80711583d039030001c2e050780c401050802091005040740b9001801200506c172100a9448003902044400042c0200e00d00040d045c01c5030043c1c2301f640e000d001110f001080284803410b0a07a02002200c04503a00071540c1d45a2200740811120044202ca0942c402403040b040840e000300a0f14400940352101809100031100c009070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 653789478 1250 653788228 653788241
    0x15030b130603060e03030c0d0c0e0d0309081e060f06030f0d03021801080c071119080606100201060608010902030601030615050310050306101a070f0807060606030b06031f09 76
    0x25030168030340341c04109005261090801c503034401d10285d851403400c1c141500c10351040c2080015150395580030010000d104110380c62141c10002c0c002c3c034584c0458100104031310142e000d001e41a01230524a058070740002c5801c0c3c1d910f401d01f50094a113943e107a24010500104c001c000641500034441e441002c01030034403c5640c10441c5803001a11051148208480c0780d60044919040c0031028040c03115400c0307030b20281c600699025440081e80e22140000c910340c00b1808404030002c21500e1030108a10801084640c45000c040c2c8210250384003400c412401d0380d100d403242c94045100c00005102c0702c8102d8000356800001814040f4900d561440710928902c072105106000a0011060000842403410210014801200200341500300b01c07000f0a1825080c2c032a40643c0e1849624003000c007900c020139140380c40e070031a80800700d15007141008403659000e01804c0b10103624000020915500a10480c901c044001e4042070651b55501080d0705405668203800400b41c003c0000011080c20390b01508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 653790728 1250 653789478 653789509
    0xa1e0210090e01050d0305120a1d07030218041e08070c06050903100c080705090a030b01030b07020607020f1b04020c0d18091a06030622050f06011815030b 68
    0x80c1d080a1910303004854100060f008a4811140002518003181c2d0100c03e80e462a8039007188071a0688407404924010419071100c0002030540310701c3c2c9102c0c1c50380800c5040440e4020f54400c2c1c082807903428000b50030181110028910070050400c1d03401c0b5108140380c451072603c22044103180c24400d88854084002541c0403e0001c0d50002c0d04040794201400491780900d56007074280100a114075003c0c2c07013000c00034080001c200002c102c6d82030582d00d41000c503006507040140401e81d0f50f101d05000295403021117419015102e01004143d1076840010310001144143c005010069510000f0490316920b041c0e07090342c4260240041504648240a6240d00010300e131141040d00d102c68050800000355584166070407440d000e18010341c80121005400c0b891400c440081c0d99a035144001040c9910f82c50103000d09041d04c0c0d00c2d804d080c0b03040e039220328090400e05022458980d03030030b001110078030038004120000451000d420001580f50240980028a2070705000c5900603d201c003182c23038000c4000780e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 653791978 1250 653790728 653790737
    0x12050405031918090507030b0a0b03010503010c140702060a0c150c11010903080f04020406030c080c011d010516060e0f1516050f070f0206210f090a1e0210 68
    0x581ca0b2400350b95102501c0500e99041c81c0800380511020100114840c2c0700e40300d5801e86841c0066a0390380300340e110b0001d10b180141840304031078076902001010707042406458020346c6003280103008203008900c542045c90a01020724a8000d00c0d03424005107401041e1602d00f48103d07106030364005290580701c0c0601d001401c0780040c84100e54070004184449805074001d40f64540b0508201180d8441c482c10f40c00501c451072420305407580e02c04640100015070015000307810483c400328564001091b08010344000341d80344a00425460a00c6815180e0154014003040d4100b00a0b00c801240d402d48840081c00b4420000c7c4056012036014107110724150301519641100d0001d103015a0b031900561f410240c1c00049a00031480428003401c40d21801881d41070700303200403440c0400c1160701c4180e643c8880c1c0c0681b20030f403640e00600c08410385a1100142c43c501411603400140301d801c683e11420f01c141125030082810303410340d850780007001c0710b42d080f081c001400222041000da200c202a204206141e65039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 653793228 1250 653791978 653791987
    0x118150f03141213171509070602070b09060a080402150c030a02100510031b03051501080c01080601020c06070503040f14030d230307180303020304050102160e15011205040503 77
    0x15034142003500505000032841803102c0e40945482841c1082581e804843c0e1a501c908172410203841d103da400c10b000d074115441000c100c14507034081140022500c81d034084840e242d880380303c490290b008407408113801000500034030032b08502c114119a085800609510788a000c1854546e0040d0700007034080005500c00600074031100c0c3d04100c4c070503c044d01c0c80c2c1c0412490918200e180d04e9800c451101802c0849103845054001d0b841148aa00540e4440100d442c1c0000b08101010070304024030a50b2541e0140500101203940244500c501c641d505074007802b91300e101c4008004898002110994540c03006110104040d2014880c0d0806031401014032800704002d14101464084488100800c020b41c00c800c0d0215030814204045131a46c2c810b0509451b599901e0040b14419842400c0902d03954130088000203060b00400100280c803400e03030903502c807001d08030f05c030b00300440c0c05100700b4010000e0880003d06162501303280000c10030301450000742c0e00c440d5080c1c9405a440569055030280c00008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 653794478 1250 653793228 653793263
    0xa030b0a0915050414010b09031507021b0d030807110a0602070506010509011d0402010804060b1c02040c0e03030d11090d060605131107030e030c180109060e0118150f03 74
    0x302d8500040504139000e01003668601c031040f8141c141031090a6154202043c014181e0b501031010b01400c10105040d82d02510b0800f1001356989809059000c2c0c107081000c2400c0e41d803c01031040142a500341d1941515510f40d02c40807145210781c03c24406540c01907422a4000520f14001010158004e00080110b94100070400500400684c00380c00c000e80f1248410800d0b1038070390207003540310380c090030884501ea4481c00c0041c003030042005101d40c06802e014642c0300c4803615094403015030f0f00942d070411184281d5002a254001c86803001a4543d000340801025101710390800154801404500c80c1001d1032400070a042400401c1f0441d070711a11040280007508040c40b500c1e001c001d0000c014480e1141c075880c03c12940c8141c80c0040e0410402c0c114800c1c180e101002640c0e41400d010749144c0d00c035619000021840c00c82801004030701410082d000407001508030585068419116a100b2007400c2c1c2c00100d002000d4480c013503840d0b4500090001003900303005644900a50080100d10011480c07070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 653795728 1250 653794478 653794511
    0x30a082a1314030601030b060a05040e030304110105091806130606020f160303090e0a2703170408030c07110913030f080c040512010f0c0c0c0b19050a030b0a09 70
    0x2034115a40c0481420026912a64001404c0e4112030b00807980c042c10b611500041010900c5541107107402c1803c1507000b408404000000350f2203680100c5182e4400032000004481d50303c1548142980031111520080184a517410455002100100300591031079245103800b058a00319800540940c0003814104455003041c04004002200d220803d42580c0c19680c001d010203007036005c0c0600115a1000040500409a11004550103101c20401c011980c00c030085282080d00c42c403c90010341014850203043e5921443e450142e40d102d113840382150b580064101aa410414090703c15000302103103510030351550900c4601580200c0110903039009242030260480e80b4089200781045841c0081101c134940d50310070b82e03042c1c078401c4075003042d5010134061a6024005858545842910b428001d1000300d8100c03032040d15a920600c0744811403645c601c41102c15004403a103800d015446080a284214802e400910b070403a038ae4140000ca11400350b010545447d0319402021806541d684124410f210781d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 653796978 1250 653795728 653795767
    0xa17150102060a09050d03051f08100b0909060f040203031e090a1508010b180312070b0601020a0302060c0901110a0f0b090106031e05010b15030621030a082a 69
    0x3c100c051200d071041d552010355507040c1c2c807421010145d0b01c0d40841c100034946140b404403490360b00720800781c45441d0112991203152401c503031282d441c0b410f5001c070b1540c189a400103103d011854040c2a41e55110300c07444002c40402401241c0c0b502042001d41412a40d10494000c5598520f5402e9299901002404006902500f1221a110204603400c1c0d403035a01c00782140c1501c1a0003007241d00c401268403803c0c41094800c50f829414059581041030a2907000b0242041d28041d1034500c020303445444c010781e00d51a0400e00500160818400104403502e5900280314002e07042c034044884e90500c101d55420a00c2c526000c1396a8407910780b6a0007400b02000407244c00929800003008428610381d0f80112001c5010240700a2010078001e140c1030200a500221000d030f0701134401800c00300e49000f080c0580d44202c646510440c400e40a09207801c900e182c00030a8030b500240118506080d01c40141c600e000e005014a441c69015030140311805140101b00d00d8005850030400d84814110240d550000384 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 653798228 1250 653796978 653796991
    0x20c01030b0f1909020d050406060603020a0c140703060e0a06050a06080a0b0c0d0203180120030408030405122116082a0a0909140c0904020a1715010206 67
    0x4001c040916a0395030025100c5000e000c0703844140c810304680f0307010007544182c0d00402c08a0301c0458840c0d03901c10b8030b41000348103078071030030f0200115511014280c040b400f403d401c079000220409400c200041e0310b0052200c1c14840041221000c80c0c0d01e0381c83c0700035940300040f80b85194200c201400101301280c001c81d030b0030200000050017601d00f030003c050380c0c4e0250560f0207012880c00b4404501025480b0301203c08a0501c503105558916003010b5203c080c08039501040c14540c640303044400c00880d85049180407400e40090a03185803216240e8a0040c0c001500c1614240101c0c0e02945007240507400504001484008038940185900380c1300641e000001c1c115122082c00150004010340c3c041c00301d0741d0000300f0320120604075002c4c0c0080c2c4019003400000c201050782c000343c482c0c0b085070810f607031008440d01e01c1810301c58010a4503600790b84a505031003540c001e1310240203d08052500341c01802c00504185000340b030340c008000c8101007144c01a90100444110452080601e581c10700401e6804039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 653799478 1250 653798228 653798231
    0x6030509011b032711030f1501090903020f0a0b091506100302070f0f03121b090509070323061002060709030f080712090501030e0705150f1905040501020c0103 70
    0x48034a891074400c0c9800541c14400c0544ea03180c070340c400c005007038845203160406000340c041001141c41d04030b5070303803140501d4280700e48115070f03014080303141c0017640c02100002c444880c00707564641144d84e809800c0c8128110b05500580e130b501e0300401401c00c440c0b01003600a8a40220f181003c04089042c80a113105110000e0b0511040050304e07161a01c0f00d850b100402d25006a590304981080880130084140082c8400c0c0c14050303500a06074030140340c2c5c1b1220030040f000c1151011703919500e03003104403c0d448203010a003020000c00c50b62034200c0000e5070000d010304001c245100d0030703d02c6da81e12100064000c284102d2540c00c4c0049401c2000714600d51103240d0000f8040c0e400d11040282001000c0d110042001c807403513115008110307010040da8401c1340d118a038036291821244000d02102600d004040c0001c1c9458204e40034100001008011035402074032045c41030604008402c01c540c401100458100020064480320b4808002446030184036542c0319500e850411000a060103200ca1a260425 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 653800728 1250 653799478 653799491
    0x10170a061a01020a111507200405010513090302010b0d080c0c030a0c0312020a08030c0c01140c0f091f0f020c011409040504110901090902190602030f0c010603020a0b040603050901 79
    0x143d03000a200c0c072a103030700615401d21034064040022031101e01450f217081d0000e4003003120000c0241d0005001850050041315101000c030741e106001c02ca0310240320341c43d0304c038901c41c00c1d9014515940d480310500d2402840081890340d00c14010541511812404a40b0b40c0000540340038641400c0c4200f07803400b08104c001d826210340d00c0d190611202d82d240005084c00c018a01c0f003265107802000055601548030345103c0d00d03813401001c41c100d1381d005400d04012550a0400c00841e8030040c1010912071503a00c034004d4100002034000650039005403212580092019000282c1006980a41144181255520340b11108011070080c20042000d8030241440b68007400300c1081c0500005940089401b900d00080d02d03a150708001170240c5d461800190460503241c004100415507400401000380241e4201c0046000c0d0450a52089031138414400140c0003031100d4031000d201180140710780501c805c00883c00030344035000501c2d2041107610800d58800c0014081043d00c0c2c141c000c060340035a6900003003040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 653801978 1250 653800728 653800781
    0x1020115080c120a061e05060108010b0a030c0e06030103052505060708090d06240e0c030708070c0602031f060215070819050a0605031e0d050310170a06 67
    0xc418001c0b00c054410303110300d07042807800701d010801500840e030403010512400385464071042000c4001082001d49908120004400b54090a1980c1c1202d04501d55940f0f000c3c49400e044000f01020412242005500c000494450b40c0d4240654003860151000d003402c1407a2500100d10850140200f0080240404040041c0e554000a50300015002007800e03aa030824440011041940040300601c006e1401e4841c0e0030040c64058040040c401141c2c0c0802c0090701c0e880e520301d20010807a032045440340200005846544102c5002c0e822072982d040079141c9000566542d01682c000304d50132041c030a51100c1c4c219204100340803040c02003009001030503110075840240705080300001d000106002c0f0402c040748001642124102d02c4400100302040f480c104891010f01800031032103224464450402d002665404414031200e41c40002c000030311003612107000540ea15040180315000e180d90500c40000d41c442c3c3d140503241000445405003641000c1071800504546100741c61800507004d009003002c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 653803228 1250 653801978 653801983
    0xc03010b1c03030207060b04020a0e0306060f0603010911040e151807320a12050609011503090609080301030b090d1416021207080d08010e04030806060a0e10020c0102011508 76
    0x46805103401341e0b0319001410800050158905015040303032000400d4480d89a121410305501c03036048080e600c990b22118200200500ea1610f00f59000e42d080004016140d0b190380168410041282e495042940c0c07605503049080044031202040100c10341c1d101c403240707005441003139041c0c101c0c403070210f00307007401e500051a521280d031000c1ca45901800070810300d40300c0030121500c03501c42186029035a0005a9009100d800202c08003207455040c10b000c140c0c3d51820800c11816904c06848030381c00c0c1001c128048015101d1801d081d85c01d2965144160041100c11000b540030b180207800d16040c904044004500d805102510b5000f0829110703040d4469407841310403a15654640e03042c9424201140c000242440340c1d014030820244249000000c000d40080381b030807401403941e19011400d03039941c00050009201110001c00180845001600300e290400c0a0b01c0c03219030a1426620b0381c050040440c0c002d8006613480000369000d42c0111140d5a1b09000d425508184e81782681442850031a415a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 653804478 1250 653803228 653803279
    0x2040204030c150206250e060d060f0b090d0308041506140f0d0206090d140a05010506012006040818030106060905032a06070f08040b031008010c0206010e10030506090c03010b 77
    0x130031840154541b101d615203e1401c0c0071208030024000c69030fa042c03e100e4900201418450186020b003031840000c0c1183e48101a106a80d001030003004036540301c1da80890308854002c10031150080740e005134181c1e00b89148652006007888140034043e540c4080700300105080340c040d240384144003500c980401603c0f1082900c14028062300d21003c400c8681c640740c0030072660f85920403082c0c03042d400750358141700e4150803150180e42c0a1721901d005426409032501f08803030a034821402e5900c174102240014440d24020000d084a2034182204105a0b900084c292065a03000e500004c1e40f6a5082c401460107100380104c0c01030030220011f4850541540000c1441d181016a115020210310101480503a14007030007041d5003e40e141d90b4641d01d6141c814025002500c9552004584090200c0c000b001449600c40b054400d40003002540e1074074241c0c596550008020001425075050004005042045514007810501028000040381d603018917003180c081147e054400c03504008070500c1d00740061041e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 653805728 1250 653804478 653804521
    0x2001090b011e142206060f0c08040614040306090309140d0b0417070b1f0b030f190b040f091b06050d11070b07080709060206091e0a02040204030c150206 67
    0x1c3c244040e66a001840203100b060b20a600401d0310024800105203e070b005609803030b540e40381c0c00d088045045007202c0d030710036045000b80003034030400050102c0e50060403900c0104a081a545250689907981d12050320420341085003c44e0b0700340300c2405140c903480844444100143e813148440c0740c1a031152001580f0207403010340341c400b010319511551200d1504951050750400c0d00c1c0901c3d414500e610602d5024040030403a01c0801965010600c1205501100e001c0c880401007a040c41c3c84403181d1043e1049290001c1e224107580c2c00003107906443d030f0f01540c6030b00c5080510004400e1450b0503e00078040c6003004c407005c000c0084400744122904201902c040501c4960002128901140004c03c58401c1d55000b5007150380e40002c00640c160302209462095079140d40c0c0080540e51441c0c142c0e034076003050310314501c1908003002c0c00603d2050740241d4803003074661070200c400540a0b500450108d03417003904182c0340807100c0c510500c4500130005078201e01545900c000c0401c0d250040d120418074a01d490031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 653806978 1250 653805728 653805749
    0x40b0f070509090402131506030c08060d110d02100e0a05040b0d23060f090c010908070519031208010321020a0b0901020d0c03020307090f12080a2001090b011e 70
    0x3203803c5d916000301050900a24900800c05003440030000701b0213522600c01d03200028101204c6100b02480f40f20894041c900180ca00709803550300341c3e0b800001c851001c2070039400558084480002d40d803142103089814030907840d06083c2c140b400040c00103600b240e400981c01507007083c02e2590b02c0d071038030040664115000001c803001c1155034520020b1010250058041c0780c0b013040c0034040c0e10086100300c1c038080d14554085408904c02d00c40152081c0010f032242080c260010746003007209051130360031120a0643c039603212210544a1f40c900c24480b103000009000039041c0e100600c10000b000d05040900c180490700744c074960b01050700081d940d11884600500034030b400004030b6007200d002d4064a00d480840c0d5401e001812002e0b030000c2c0250401c641e44d84c001040400c0c00240e03880501c4461090b107641a1900d6032410032030315400585e601180d14141003050641207240500f0700380a0b08001e046034800007041c89c000a0038801000d0700f042e08000da890345070301c4a031600042c485e00003000b02c4141c1c190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 653808228 1250 653806978 653806981
    0x70503120c03040306110414040519020c030c0f06070813210306050d150f020403050a0b04020105040807030b011a09011e0203130611060f010605030708040c050d0506040b0f07050909 80
    0x1010b829401a540010b080754100b000740d00c00a08840068000c0d1a0350800d00c0c42407203c44030402c07042c0c8205442e0f10b0400044140150403101132034004120007008002268030301170314007200d1441d20a01c03882401c01a0415010300c0f00c0c2c194010314240d0082800c001c910074080c03d585a000da08070500c80540b02803c548081d0003003082c0a5045203008090062061050031311070f05000d00c50188001000041903d01070403810307501042d1003501d081e66040350051201841e1599015242d9802810a85c144841448001001c001c20401100610710510404025515147c1d18080c0d0172864040101c403441309005040869a00200b154892482c203060078036110703100c000c140e086101c0c1014095282110300d01c003040c580d8001c000c0b088800449400c845480d83c64410301e50b5080428018440001d00400102c2d810a100e030345102c1d085800703031f80d011000c02d41d80c2d0005a101448c0540448150300182d0070081400104101558811140d080743d545625280c180186a8810030351264401c048640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 653809478 1250 653808228 653808247
    0x1802090315071808011d03040602030d050613050c040314071a0d0603200f09011202191d0a0507090602060c0c0102040506042402010209010806120c03010c08090f07050312 75
    0x80d000c00f4a601c582d50300048282c03112101c1d40a81483c90000c2150724003407110740d03c6a140081250120303991a405035041c107140b01092005400e02800d915801158009001001e10051283c00c1c01004484030440d1340310f00e1403500036103013010103124604c143c00c1460100a2404020f8080e02000f2075408810341d982e01c4584180003d240070381001d89548800c20104881c008441560340c0300c2c0702c0861700e207070069001504005580704240203020340c1d00d021010040040c03c0000a403104100c0d00003901d400d00f51502003606030a15940400d0002e5000401030003404192486a990015414546803980f2824a84043c1d82d0b000054207407001c80b071001404424501082d810f4401400e4001d0401da40c4a5995860b240005208681034a000d0200c1c40e80f00000b600520882d00421010b8440c0492580c0e80c0040100310681c40001900600078003049920582d000e105102d84c0303c0850f21400240d05200107528600017080e281108141e2240c1c209000941d00058030b034038481c50000c0d600c1c3d80d031071540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 653810728 1250 653809478 653809487
    0x306010f051309061a0c0c0d030c050a0f0b0903070c05090903041703030702061e04080a03022101032f0603040c0f030803041509031d06041806180209031507 69
    0x1450303107040000c00712008625070f00c21350080001ca40003900c24215040c88454a05440e114455484086a001d10b60714652410001d01c20b107101030103400d2000b940c203419282e02e070401020303400c101d0740401564011010083d03480c44441d000758511000f5800c02c407081e6182e0342c14000c14020030344100ca0400002d9001c050800480b030140000452042d8600048641c85580c1c0d00142c40300400750040100042102600041c40c06180384081154a140c0c0c507070352540300250f0710000002d0b0800d5000c0000b500c2a100081603d0b01403403c104103a8119132441c202042030929a891081d0004030000c55400c0030344140941403a5044100d0340190b0300d4440d85400045005179502c801180e1060b01800014022280c1c0a54450350084801000c0d505580d543ea6044070420300b40200030860b51410003451030240c8105070709001d400f0b44010301d0543c542e41542c45050314a034441c01002c2d1103410a000d107024064070380e1002c161485040d070501651400103a00e800c0e280d5050b50100c04c2640020300d1040c0701c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 653811978 1250 653810728 653810737
    0x21070f0825060509010b03070b0a030603140a0203100e030406030b0a0e0f09010605030a1502070311071412011505060a0e040f0902030f0d1d0301020c01020408010b240306010f05 78
    0x2051816001c0d006400041c2400c0c0300c1c620300580ea0300380342c0703000070b40035210601030070419078401070152010703601b40060111150400708000e01015961070300400000c002e00140c815a40c02c00008000301c0703121b4130405180a40b1401c2c0d015004e401c100c922000070000000b51400e031000c0f8140800e00e8103000000c98420521980400c900000007424000200072148c7c10501401c0648000c1c840981c0310410300d640d9009200004202ea505052a0300901c4195405808000d2080c17238041002104a4031581c506905504503251392403581c07003420340c1480c12803030305c5020a0051000340000b140c00e10036040144ca0301d102d000c0c0035050005980101511038800b0300100c00001740104081c0e07191070b100324005c00107200124002e108170070900c010401d000134600707a03d01a0743d45444c001c1000d04090a02c0c0c201c2401d00710341540d0244490642c01344280003801c058556180002080b9040c14200840090040d01400494000b0741886104121800c1101e500410a0030107250200345860115018400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 653813228 1250 653811978 653811997
    0x120c081b150a15080c0d020f01020c1e010210050c2b09030e0a050f0f13060f031203050117100b0105040b160c06050a08150609091821070f08 62
    0x40360001c11120208541c85a1105400700051182082d180e07543d440e0341305014994168040141d061b024010714003080b526965803010700c1039680a039506404109503000d03884011941c030b17445030300a05c140d590421004c2000f105803d4144028200340914080340c3c0710700814050101e106c103150114845404000681d200900e07042000550032500300107040c5206421020b20a5800000001b51858408490b0a48000041c9140302c2d40540c84100010502c1402a400010b910b400000039948a091070080040d4010900140c908130f00c3c143c0101260341c145c11075079085016100d00c1911440024000c01c41034044070000568510030001665540500e5008502200700007944803503407048030404030300b124401e20142c100e803600c031407054034640205032045000a41c2c18000840e042c0d001d08054041c0702000c4c05282c074100d000d41c0440d8618008036101b04101c103100b210904081c40800001c4540d0159407440c81014001142060951080b02809040d01c00c3c4074402c9024040000115042c078079 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 653814478 1250 653813228 653813263
    0x1107030c08220e0717010e07120b03010c051305011106040b190912080a0c0507081303060e0a11030309010507110102010f0c030b0112050c04050d050a060c0c120c081b 73
    0x156104103100750103800310790481c0011035030300d002c80e520100c170f41446042e40e0801030b2201c1c031581d841d4011a1807038443c001c2c80c1c2c0b2700c6403108180b01d421b0300c0a200d000b103680b00b035035070306540d502d9400118403641c4999480141001019a00c07124520701c04140640c100d540300700c4461054417400c00c00803081444541e003241403031410002c402004800380c050302c000d10705070300d81114903914442210110781c01c1500c51004550200802000110024014030200043e010895a1951203847e614110369080320186000c2e403050303001006220070118902c124200450080d468400400002400d90040f41d03001461016402130380c0040b030b8000e400c008060001c00c0e20801904040d410000e0281142241d040e01040c0e02e82d03801b003044d000c00d005080c030032020344500720b19141c500700a12841c14030000c2c0541e86409036820250000b810780c028103054648590380c029002d0914104504030b907551403c4241030000c44000c0c0c400049000701603c1d561144000f00456a60790b100007182020000c16841c103054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 653815728 1250 653814478 653814547
    0x1d0303061314010b07032c010c030219060509060c04080316020f0306160f0305060a0e06010c0f2108092a040204090606090b0a02030d05060f0306040303050a1107030c08 74
    0x48001d9805040320a0203956140003140742e0261a07002c0c4507415042425a5000c01f0751030030b265010b0019810820300c2072040302d40b00050a540c3e0006900000c50480e85107407aa0203008a54604006072604401d4035116285081e11b1701c030010b5030720300c128160705402c20075050340c9000b076688085882980b540050b00f034682619000303170005165140c80c00c040700840c0050f0180100c19201c0c1c480c607881038070041e080800302070905040703007441c28001b404941000b081c142c10400089850703400c011501d114104a903052040f030b0400840341e1804520302c02c00c02006204125452900052a0790010241c12a5242e005008030001e0400032113251044e4201e03000180014920501d94801e900715940d03540c492052544454103010148a01004800140e000707021503050390445520407a0003c00c000d0486c880d104562000c00d0910b44200c2c1d0a03004681c0c0d4408020b4044041d0090044a1002c9817445d407610880356030103419503c11013400b605000001c5505d011000e41d40c2c0c00c24414141a40c00d0245e81d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 653816978 1250 653815728 653815739
    0x501031d0a0f02040c030c0917030f0705030d050106031a09220803060f0108060a03080a0323091b131805010e06010315020703080705131a07061d030306131401 70
    0x1810102c20220300540c0390803c4010080c3c4a1b1055a042e41e22943d504400f00b40340240c2200300c1003151401010a0204121101c000203a6100402100344a94083d540348c05420410b0380442d0070582c0034605250030301e0942c0c00e02c1c2c0783d44c17a03905160310801c8a80003e036031140800702c039035840c80c01c0300302410469500d0007105100050024500c00c000488005000c0c405490044946030300a441040c1c001d1002102400003c90780400303401d480030702e0b10740001c51810458403035081c64000a0010030a68010091108201301444881400d840200008054910740d03004580420305144428000348c0e61848085ea01d024480c030385400840c0c00c10001c0c0b0241da1300c004001d032108d84c20300c0111500800110351000c40300a90003622290790301520f42142c3c569074a0000ea410b0744c4481000040c00c041aa40403a81400d90301070b003007140c0c45595a1544034040c5107001c0c012615400c445040001d100074202d01444400000c40340d11044c19540380c400301805420081c0941400c6001130300b01910100007050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 653818228 1250 653816978 653816993
    0xd0b0306070507060b0a050d031211030a020406030b030a260d06031b06031506030b0d1b080f03070f111507120305070e0102061503030c15010602070518010501031d0a 73
    0x70743e90700a810800c800340112040040700e4500c2c0c410250404018514840403a008507007042000d00902030115a001c00d140038110942d204031060360046902080510215a00d03110301d8420807401d8000707040307014164480c02030008652001ca50440c5441120384805403502e020b8841c0e0b4045c01400b070103003907200d00c2c04038000344002c14004000b0b5240740000840301e200c0c0c040c58842c461103905101c65a4140101203001d40542c41504d90000000b4080301d000425054209080400441e0020240c905100e50f0310706214031700f0b903003500e50380c803c1c0000804900b0103842c1e0030010742d2201e1028504400c0e040400c00c0b40103d00c20340c0c0d07507525001c541d680500440780803820500640c0d5034100441c0c0c2e1034280607240003038000822401a800034001132100c04003085141180800201140e0800c11315905d42440e08580c4070700000c8190850004021150301005050007800c01100c2d19032003840e141101e680840c20502ca20350405d17484d1001c054a460010481c103405210100a507260703851941030640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 653819478 1250 653818228 653818237
    0x301030f0308070f09090f02040806190c0507081b071206060305061e0a0b030c101d030f060a1a060a080403091a09090c2208010e030f0703050d0b03060705 68
    0x1804120440c00150101303120392800108403402d503c61308801800d00c60b2902c003d00c541c079101051203038200030100d56400f00300592441403180100c40e0310000100c03060103003a5119900044103024090018000245140c010741c1c0c0f4545000245004014044405524051803580300d200a40a028004800d04c840c0350401010f42c0c1c051030441d0031a0f00c4503042008105c01c1070703203014913400819020810040b40c03904440248240241103030a11418600051640c0c2c04c031081c14000b066184c0452006200c10300b0b0400c0c95400e0841c041d00d01503c1c60202c0c2a10341c9401011314040d1561a5041c80410241e890000762002c000740805458480319440584640e90507201138021540d50200000ca089050b60543c40d0280c01e50313240c608043c1d80c20709001008101801000026000707005110a0140500b2072181440e81c1012401c0c00700d203065003c40c2111608110281203400c01c002c200303492402d10301101d084580c50b181040d03445240c440035000402c8030071a05a8180036460a000350b2961110181 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 653820728 1250 653819478 653819483
    0x7050406020f0a020136080705040b1c030f0c0b1504050a06230a090f020304140304030c2c070203030a0f0203040210320d2324060301030f 61
    0x1c038681e4035041c0c1c010f9036410b54100004d0010322084448402c5840303102d12841d1001c0744410300d500070715040c2c02c4041c01c242c032a00121840d60292904101d00c0c549070140440c0140103488422480d00c2c10124880901d1240e1406018806e69031083d000481c45912000041e94124104003581d00f0b24141801401042103032003841b803824400825803080040c40755030101c0310b1000c3ca101030b5081000400d200d0b581041200d0303a10004103000028541102c3c0100011000c7c1d582c001a500d01e00b501c4c040c100300001c800030f0101c030391051000b4800150040c00c02e000340ca00750400c490380e070450075540101190b03a0400790524050300b04244010550001302a5000700c040e08002d002800000203a1412030004a90113540040c40002c40351459008418000300b40240541c60901c8414100001c2c64014040744110501c0318009952041c08030948103081410010000d41040341540002d529070403400a0b000500300c030f0000c0c040c1e208100b83c619640380d0071003000c0c020303a403a580d490034010b00c03a2041200c113 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 653821978 1250 653820728 653820733
    0xe071d030d090315060807030b06101b02062b0e0c2202131d04031b1a06010207080a0b0402040e010b15160209040f05010f0615080912030705040602 65
    0x2505a50328001c030710242072000540c1c60034040c52540e1544e590900d110040150501d40d5400d0210308084144800006540242019805420031405119141919128000400c0004842c4140c030050030048000516011900300c2d8444c1003a54500100b064a401000a0900200e500d41030603e4035400c200140300c460005c3d00d2550800c00d090210480941000b40c10f010900043c4640c1240240e0260035a0314980c07540c030350b1064481480d040c0d01c500c0b9810180b100c2200004120804da80310b45001095401480035031000c400076956840480400d10000400d0381c900000501113920810401c0b000f080ba98041700c5818180d42040c244200080d10164021070910006040c40074050040da070510401030b0038500082d901c0c40c0f801401d40c201c094004041180110340c040945d40f05c026060040340541012116444145891401c642c507046c3c407415a9810103108001c00e1800240c04d1940c9840c1c4d0418049941d51402c0301806c005002032a20854040403040c850842c5c0c0c070034040e0096801c00d808 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 653823228 1250 653821978 653822027
    0x30504061404140c0616061a0a0f0f0503010207020d0807060b10050c010e01051005120307081206011b050303010506070c05060a020309010801060e06030c0c0c032e0b1302070305040e07 81
    0x1d0060300d104003010081a0300200c801d9100150540d400f400740143d43c103400c0340440c00a23400040c01c2c02800c1d80001e1240c85200000c0c8003a1001c02445d0000784003c0b4000c500c0c0421643c0850a07018014401400402d400b0444100f03000481d00861041880109244880d0400c104c002d0304035048803008080d10b40c60420030b003560f03140511a40340540c8039207030441151860300c000c001125250003101c032403600040c007070f00f000a030991014202099030051040014600800010f00305504903401030754080c141200c64002c00d81c08011a815581e0640c0e44a582d560242400b41100c055030340708980110f800118860266400701c05000c0d0f0300c0e4242d03101f48140c4d984480880306024442401903003c802080070030004c2d45241c0c010f11407410701d4020303105400e08800020341402138440c2000140039010101403000061030011151100000744200204110000030454040039104c548d50700382c0d400195002818050070030395004003000320011113103203003008005110350364041c5d188001e10320402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 653824478 1250 653823228 653823253
    0x6020f10020c0703060e12190f0f170711060112020405130308060402090f1e01200c0f0109121a0a0507124b0606020d03050406140414 59
    0x322919a07003a20018501c43d030071503c0d100000c0c808101c07981554804c188140c02400305d0007000c2d1a10f2840003101e6080fa56024101800800c1c40d18481e0007000f00c1610346400c02a00134071181031048002ca05038000d039035a40425100701c0c0f00b0400c2c030241c1d0b05c12600009000f000c51007519000c103100355403d02050721900c044080300e0a01040c010042940580003484a017440e5002d88281c2500400302c2d4041c07010304022440c3c010900b8400d00d0b01e554a0361a4551750358200c41e04410750405606400003100c2007140c00da0301e0f690300041030752190101071680f560b00ea205200d0f51010300b00c086035181c02044d092504146541c0d0301710206042c0f20760280010401e15042c42040d210300b4080d12800c00c43d000c0d03d01103034000c001891034542c02440d003603424018219140b80d20348941000e9824100505081403c044008010ba10006009810510213002565000c210520b11040b0350070007090b00d440301c0c0350010141203555003003c03000020208110a00004c8410180041c40030000d541c1101010f1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 653825728 1250 653824478 653824481
    0x3030c060a11090102150703060f141e22060f1e06081b0d0f0c02010903181202010f030e1b0415060504121a0705030711150f0c0d0606020f10 62
    0x3c5081da0251300000860980d120038640c040e64001e415140c00290a0340b200c008080011883d04048007405170240300c0300c02400c0a4180031081070340d10b4818152420a880040e00c5000d0320890004400340c944840402c4034655007100300541640c056000790240c843c0035038144410820021810b141901e40000742203409003490500540b03180715420b035006044007450000342d00140704806040e80d500024050003459100741103080f802e40d0b001043c01c1840d810300400005048940628900c20104104440013005c0c880c05070456084c20540c03400c80031510190024071117400020304500403034108028000f50103d90070204170f4100d804010b03d054110107104000803d008036804110708210070301000c40758129070b0074024450351286a040d40c0b0b1052220f1407a506a4543c800702d003010040c42801a0000b14010311130562070010003060b80d0407511030000031000307802006004007d07000b0600c4a07800314116014421201000e120040e96090025681e04160b02240384030b0195890321209003200c4d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 653826978 1250 653825728 653825737
    0x20301031103240a0509151f0905160f05120907031202060601020a0204150302060f0c0c06030c030703181e2d171219050606030c070f020a0503030c060a11 68
    0x2c4001ca83c07055901d80d550740005140142a00c8410b2045a28101c032140c0c5c0d00303551500c51071484c3e100c1d00c4406500e07040e5200840e00c40e00411f40241c00c11080110702a91608a0220442e10b880c0c0309503100708100f01a2042c0c03041225940b1a501d001c01080401000000c110003107a1203055410301509840c5800c07615894180c6001c4d005800c0005101d02518213a004982c5403200c0322021580f1580e00da0018955034844043ca14003e0400b2542e404040c030180043c04c6c1011050741c60034039610340703082c0c0391501c0d210007803e41050540c0d5035120101041c407518229000341c0c0c4194a4440000e0b6030506141902c078205040b00c0041c421900d50603240c0010594020160400e41c607420030714195500c804103119041040b401e916030501c1414128181501c010380554011844100d032030200003698020f0741c10090285009141c10024482120744507821141d046411510040c41c0305010701c0090700c00c881c01c1d4410b0754507200c081900210300c1c10219159014002c100810044116600440f816038000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 653828228 1250 653826978 653827033
    0x608060409120e03031c09022103031f0f060315090b0102030406031a04150e0a09200d08131707060f050d060312050706180b0a0f020d020301031103 65
    0x64145071910164000e43d1520300d0b224004060b242030400e030601c0708401100048005010702e17100d036490829801d0541c4d002504040c210b885545448101e519180d481c40041c2c0b2203612200e0503c00c8040003040c503540b01010f00b0242c080003296581d2108003d01828042081d0201000111000904a07940d8030490704400010780203141854a010710640c010304143c100c41d103042520149040456480b40300340c504940340e00e51440c4500b800d0000c071610364440244640700803450700c62080f02142c10110000c03601c2110300c4021210242d09001710f00103030f8462100030420100850148035510504804070300b45c07082c02d40b00b007050a14400d49580e0b00d407042d03c01c02010406054014100c07d2142c8010305201d240c40d40042800c0303503a5035812150080c4040501c0000d1004250b400802185010300306d07406402c41c1003000129003603260140c42c1b48000d4640700886940702c4d00c6d843c100c0650340582d14400d9021074219102e41c0e59080c4042c154200c081d00500c207001d00c50a85039080307005664a091100e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 653829478 1250 653828228 653828243
    0x10c020d030f02090d1b06020c0307090e0a0204050a0e0f120712090e0f0a0b010c02030709051906030b0a060b160b0c0415030e07051c02060306060909100608060409 72
    0x144100054008002401e455a41c1c5902001400c413541c541400e0310f40194030402c030242c624549540b0b0130b524203000c0d8101000715002005008004daa001510900396001071030300040d0302c49500c1e820740c6010760f0900000d4005007000e041000c5021030754030902c400401c100648800c86181400540c03141900d2005040e020020701000b000300380001d8200040c04039a0610840c15a20341380c505d012101c046492104040b440c4080142d02d107680c1c001c81403d0031003030034140400e03032840d40000d80b0343d40103000e140d0301c2c02d581e03400080700751031907142e240f400c846074400402c0026140c2c00c0801002314101e90f890800c0b42020720018201640ca802c0390080c04c0a0a92200d16080a41c0d4910f00340001410a41c1943c005120105208540320640308074002543c07000520402d030000058109034041d48564852000b00c0c1640c0e400c0b494202c180b0918a60480c4c10a560b5a01d00380001c90758051045a160000c48202c2001506c80249503114103464190700d502c0300968640041206542806400a03c8074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 653830728 1250 653829478 653829493
    0xd05371d060d180f0b04060f0507080f0406020f040815151804021503160306050a06020307080c0102071b0602060a02040b07030e011202032703030408220801050a06090e010c02 77
    0x4814552028001c3e4218070032043d103c1c80d00c4e880ea241c0340c03034044070160b98440ca00b4003840100160f034032034200e010000c00800e0000e443c0c40200a06070900051151200c03181e075100041c2000300d01d03030407141004003004a10f130704c481c0c90f903070b1895030f1320312107100380311070802000101d482e10301d9066044c05540e000420700380b0500070310b551001020030b02800481e0429480b40324031401c0511000a10b106407a181071041c6609902d0383c0c01010b490007a8000d6015004402c03086c80004d5001c401c84290981002c3c400b41d4a60b84d1040c1c00d0300910410030701038601140901070860055409240c442282d525500310313005034680c424000200d218520955140210801080b80003a006600b00300c039240e0141070064000c482d502c03d8074103a078000c640c0c00341440501f8007130500b914855516032508602050007542180743c203a40743c0c1c0085c400c0800c10b100000e0b000e401c40504444003c815409025080001c2c000e03800c1c941c012002418003070181301c0145050040c8107a5194051107084c0420340f4660080088 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 653831978 1250 653830728 653830747
    0x90a0b0f0a2706030e060604050609071b080c06040507080106050a0611150c03012309070810080a2001030c0c02100908070e0702060c0307020d05371d06 67
    0xb088000001032445542d4a20807410358041e42c0810009265030380380410043e00100d452400d0040c000c03c2c65204074680300510a45481e503e40c1d250303100c0c80d582040712441e1604007460541c0102180001c100c0c05000851110300700012039010f0149108a08840c07903503407210409401d079500340c003035281c00a681490800c52940301c1e0044201d0b01240206940c441e000450311943c050760119a500e0003503d001004000e00395010401e8241c2c1c021031042e210080b02c84400280c10b07075502410150402c40a20702190354161040e01c8640142403250484407000700e00d01d4400324600255a14244440100400035142d501a001d840740c03030059562407948403521682040360300841c601c00601000b0402030041038945003000303108007800e241c080f03000551038110002854104010000d2352010018401d1141050700001e01c141e1850702420016228601000910341ca80e03204840c001c0d202d004844d40301801e542d02c10954184050b030741e40c1d00c0e221a80541403a1144114001c010780c01500c100a014030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 653833228 1250 653831978 653831987
    0xe070b120c0f0c070303020d02030406052a0607030c080f0f07030c02010f1103010f05060705070909061b08070215070e0f0f04050c03010f0f060f18050301060803090a0b0f0a 76
    0x1400748600340c04a041c9a90754000600e140c0000c0c400300340e9039001050510038560100658050000c5c1840114600760400100505502a03420142200303002c0304130580c2112009a1602022030403182115418030344188020040c2c043c4400d100d002c0303070003080072407117010140c800b5038070031038144003000b007241c40d003504c11401404295a03030400c556882498004e84810f034061100a1155905200d407254101a45040c00101c81d500651142104000c6503001070004501041210580200050104001d0070602c000e0180740c00742c000c001491040081489400a01c0940140c540398211140c000c1040d24403001d0b00310588151011501c20b0300c0601c020f161200900946000141200d075890880c2c0000c20309403a400c0d10040e0112a000c0f00501088221042c400020220100c1c0c02070114038249018150600d09410312040103002d040301a40f0a00200c0702c9401001c010303008104260741c581c40e0175101d4004502d5076120f204001f4000404c41c2c80b00b400d481d90411102041450308010240589 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 653834478 1250 653833228 653833231
    0x4031a040320010f05150a03080703180e011508040201120c020a0f080415230711030a0602180603060f011b0c0602060103140105090a11040605090c0a030e070b12 71
    0x400700014041d84200c2884226680340b001c090314030010810783c2500442d941583c100401600e07460704c1170780da40400c43d56010000001c50b0b41141040d952500d07a428111f4060310003103501002c111030660002810080000424129400c1098510000d1151107080318a40020340f000790001e0030030707061f41c0311102040d0b12032503044c001303401100c7d007041469070740c005504100304054800d17040100b002c104454015251145209140c45d150080c0c034403a0010003241e41400e40100311000b004900719003000042c502c40c0d0014000101100d03002071403482d01c1000f0358890790346c0700d40c0c00d02940c400c0360450500d18150307400f40500519295101c4014001103488400751501030309890071100803980451060505a0040c0036503601a1032558114100b2110781e901581c0409105da161208001c0c1f20840403070501c5840740d1040240c5451100e00d00002e018107196005143d21160040a000300005048d0052a152400380c40c144030b00825480340e15107811440c803803003c460400f0050005c03201602803074507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 653835728 1250 653834478 653834483
    0x60109140f040f02091504081c0c060f09060b06040308030604020d092f0a0b03062206121a0402060304060915110c10020412030c02060c1f0e0304031a04 67
    0xc071541d55040d0009000d840301404802d0b00a80d0000e02d854550412006c02101c0c5450f804c4450700d030600d0080d8850fa140d18084103142120030040b04059503500c1462088140c90b003006060000e00000e031601030050000e610111071041c03800c20134105504201040d07808480e0045106811130b036921090102a6011400322000c00e80e43d40c2654000684030941c6941c00d100d0f241402c036070000f001000b01100c0001400841c420303103121004221803041038045a52000c420b81d200d03101040121520030b010384000108400791801d00f000130030b541e1204115281c03400e000e1000c01407104014408130120300c07400d031006074101c602040010003054180e0824880700d4480d14407120f9000e2820040021101c101c408280451400a000c180541c010000c2121034070a01c171045251600e010b01c403901d04111580300070148440d4548a40c00d40d642c5409540350040d1800a40380aa40b4a40b11707181c3e10850000003c2c041403070004850050a4000292800e4a611440090301c00d41c016800000441000703008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 653836978 1250 653835728 653835739
    0x50d02030c18100e0f010311030a140c09160206010b0a140a0806180702071511010f020a11010209013e01020a11062a0c06070203091806010914 63
    0x2644400e0b200c00c0b40c91591060400408102d0341400c40303480c071066140703a210f1440080c00d4414000700b8044403550b20304603039200100c1c0d1140b66420001c00e052010005001d45510b4038545840d40d2400b000c40c0c8402a04400c80d1f80907110b41c1c2e04c0c0164030307500384420b5aa50050344800c0040c4007079000200181101001800e00c1010b0004060048516500040100000a088100380162400c11a1039000512007160042c0c00d5480d04410082d540c1c0f00d680320300080d483e0380c4202c90711018060308000c2e49001440b8001c0c001c1101c100c9009010f5803200f0209000203070158000211054103209540e01c3e44016510354000c14011456150700550880442d0030f42050307012030020070103010304a90840c0c107660001584404039020060000c403002e60610200d07400010402400f140034502d08908a1503580155402c20f0040c0724075400390203100340c908420300c1004140305c41307a07400001030325800302c04960480300c421480c4002c0c1041202545e04a02141d0f00140c24050b0448102c002030300188040c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 653838228 1250 653836978 653836993
    0x50f040801020409061d13021c1406090d080403050301150306051c17091809010b0d0b1603020c0a0204091b030c0905070e010c03050a0306030804060201020307030f0e0304050d0203 79
    0xd003508a034015402031240940d034a80400c26843c02032815075102c0e4080026541d20315020061000890200c14001c0c4a0504a61841003c40c0b9032034100305000e400c038045c0c034103254060544503030b41c140a45032424544030307404021500501c10768090340f040341e0594400f41164609501d0545a213000f00c6800c080c5501d4040106084e291070300f585011502040c100c40b01d4400384c2c1003a558604042001000d5000100062031240d1110358011060001010f00750002e941c40d82419801082820030b0541d101c0c0e6602404014010305084050090f800c44195210a00300d10205400f00d101e030388042c128a8011140c2e80303001d8902030340b042100c2401945804101c0c110458007400800c2d20781c20032602980320b4042030001c94260701c2032540c012094103010111034103800018007451000d00000301040000240543c00e42d1180c0c014000455020713440039103850720b51030040e02030b400880d41c40c00001d20300110766444072014000c100d00985181c003d90324007410042070100e5030b4406503059800d4031400e030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 653839478 1250 653838228 653838239
    0x53a0e060c0102030a0501080106060e01051303020409050318091605070c1e14041802060c0c060f0a260627040507180b0a050603040302150702210c030406050f04 71
    0x10010141d100440300010303941e2400410080450300180c2010003503078581001804041c1d08000c811003008000d08110b07482c5e02c26984c5119482410b81c00007904541040456005c2080010103004200012104058190310807828840c402d4012521804411042d070448964a0f00400041c81c0d618010001c0780182c0c0e07103580b1501d40d00c00704047d0a00f40940d40050820101002e00c0e240c040c1c6920403901440560a20f88203c8080d56081a0282c811000018440c404c40000c00c03001c501403101400054650964401c4828150803000419011607040b0100ca5000c0341d14880c0c001c2440080e0f1300746105038a448042c4a0510741001d11240b0880c04856045100e54800c881184103d00c80c0c0d00030200e80d803d04c00c01102c01260a109000b0703160801d04001040e03070390308440b101a21015259161241d070703581003c910f01150888413880b0740242005112100d03074041021294490300d00e2490401008801d4818598400e107a40030f01190414030092004500c01d00003842c0c40e203460707051a811b140e02ca0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 653840728 1250 653839478 653839489
    0x50c0708070f210f050f04090e0307140102120a1401031407030609080c150c0f090a0e0a05040b0c0903060c090102070510050309010b0607050c0f01050f04030f053a0e 73
    0x482c600400d8080c01284003283c070f584410490304d5034085182280c105500c080c03203003003140901d000b004043c588030026046000d40400507140c003e03802c00c1d2004038040400500c24000d5109d20041d40824002800180036500c960180b901012132501c0502d0050303180d61036a1400341d4010409510500803000d00001050081c00f40d010f6050141da01c05a88075500a0f60030b1801094005001107060b04d0800c100030301041206a5200003601c040c6c659a03180e021300003860403541d540010386400070810510540e0048c5522003403185100780f034032801645501c002e1aa15006100940358182c1c04140050340318030b862000392003098018011280e00750b44a000290326605030300c241c14000b440100070005085424003c0c008807400a9420505d442c40c1364540c1a25814420940390240e0003942c001d1010381d12680454580407048241c2e9901d03507460380b8007819096404141a201c40c4039079180d0760030822102c550f009800510240055841403903401f400614048040c940041c03110f0400000328580740c0c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 653841978 1250 653840728 653840753
    0xc0c030e0604091d0114010f15030603080a05030a0f0e070512011b0c05010b01090b030f040c08060a0e0c03060c160c03060c1e08190e0c041518050c0708070f 69
    0xa091300081070786103842e295030846211600050a908400d001004244c005402510a54202010003829200e00d984241c01030102944020500c00001502004507030380000518013521480c0e02c2032010007104828082034550126106070076810204080007240760094007481c04501c02d00002c91403101700c5010901c0c411840c900e1a0100c1c0c1c850000008001d400e115440350319009092080402d4100035000c10300713000040404103880758410100b420721081c14296002450f80004443c07079440c1450000020f0001c03900c03910030601c6403804075002c40c0380c0418101d104070514101203080c0081e02400c203500c5c580480080e0f070030104070346001c00400e09a0043c601c8800080c0c45034000c40c508251802a8852000d42001c1008589818000705000724946809440a42540440c03c0e80d52004010704101004646541c028a0003000c0090045084029401c03220b10007a0b40890814091001d0b09945007100d2004220004010440001c0c6141e0003a0144a000318440c620802140da112144d0041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 653843228 1250 653841978 653842001
    0xd0f030c030b131d15040807020111010c0e1206190b0a1815150f030507200a110105041202090a2705010612020d02120312070801050a06030c0c030e060409 68
    0xc0f81d40c2001c010614030342901c1904c000000c000c017002580802c3c0d582e118000948000c203402400a08142035a12640f0001080d0703e030f510007080f001b1000d0401600b0003901089a50041c0415104040b40c02d5012552520400c0003152101030042c1603803c00d03004000c805d0105900c841414000300d1aa58488201c6640c00195107000801159030b030183e01c240c402981c0550021000040308151059200303200c117180c04210308000c9007940b519501a946c0e081e2440c9840188148966040c0410000260a403030f142d001e1941446260044801103034603100c2c81c000e101d4090080940c401c01070400d002c9180d031058130b40c64005030342e903e6100c41c0c041c0503215007072001c441c01c502107000081c0902880f901008140000103400c1d4000e169010030f035030320441d07000a4400c50f088103101070041c505100712810300e0401c5944038400e00c2c203280060b010020a00815000b03115501c80803480c0e82c0032740724440081006450349036801d03055540454411081c3d07958a90480b0041c000016440c5003401495071700d82 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 653844478 1250 653843228 653843231
    0x3050f030d0b0d02030a030e041b0507150e0a0f110d0501141012060f020c01021303050d05090a0e06040e030c0a0501050f0f011208090607120f020d0f030c030b13 71
    0x550001c00d070300c1652410544540318a000c4440c600c01a58000303084410940c0c5410302401c0c8d2041140010000c1c0300c0d80c80d00700c1c8001e00d02c592400c0242d030b008006000291040c48800e507085041c1312240219042d803002d120082d0312041035640402c0c0012fa040441c0c0c2e100d5000108801b034442c0108440741540c40e4211801e0b9141c0ca0740c03203154440000040c1e441440810900c60f15807401a0111280c0910314020308001d9803a007000c0c1c81c145003038040712458003a18009540d140310050050160301110b00c41a100d074010640340e64005407060b4102c49181b00e000b4014429113003030088907003c844000e031100da8860794504410252000034070203070a480001401902d001c0d402070a005003035601c01441076001d960003808120010882031500ca0554024202000400700b10b172428082500c036600c00b55274002804076503002080a000360030034a0103440e550391081001101e605a98901e1000b0100002c030f0360414481c540340e4425400000416620b2401207010204000410b00b42e82c00c040201034280d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 653845728 1250 653844478 653844487
    0x50912030c0d170a0515060a182904060c03030f0e0609010f060e04020319170c010b010306090c0e27040c050102010c0f120c050409020c060105150405010c0b0901020403050f03 77
    0xc40000100c1d0303441210403800348140d1401c0c49031b941c074075290f40c6625403040c2400300b1040d0070799124030000c0b80e154074000700990056071260050101c07188110364507100954030300800807081441c2c0702030b50100c40701a204c02101007000e540c1680a407505a0100d10001d58070441d0300b0315400304000550085d400c11000040c0c001012545d401541d0b0f041d0804400460450103000040e280003d418032449080701c24402c0514091509030710040508005105001c0040317030100e4840010351000070380407400d807403c101c1640d84036110b030b0691382000d4030603000c200030000e11511403d18940c40585507904040110030071b1007545504a4910003950705490302d09c409402440656024400c030984600c850401c80e540c00140400108801029107c44900c2c03500d66144035a1540500150b0b40a80950101036440d03c2010b604c0d1036803413509205261181e001c048003000c201c080034045070140c4506039100c404003405070721161000310024008002d1594200400070224909000c1c98001c14401e8014513503c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 653846978 1250 653845728 653845757
    0x619201506090106030b03101a060d0b0301060501090e060d0203010f0905070905010e0c0d020a020715031a041107020f1807020a120201051905190c0c03080c0703050912030c0d 77
    0x400b0b016003100013410326000d0246103d540010702080c078604200c02c0811680250300e90140c2241c01b41d642250072110200d0301440040541d0010035031a03409900800c411586ca1004554a032400e02c00c510440a03060089040781c2446072030480981d0000d80003042100c041c20607001143c4a146096605401261043c4403c04c824001c2600404440740048040c4c28401c400581a20030405000d180300c0c2d0016215030302034028081d07500141902c0c1e500b070703201c2113000c8000383c0039000100e000e42c801c1120241c0900e0510b09071040c3e01c24075401480150402038960f080c000c104c40e0040300388e41d0014004501e00290b02003001c54921a113a20743c040c0050001c1b900d450b05080340100986002e690400d8104242c4a01c08205000c440e2178140002c900c90311495050441c5000585080e0001030408640c40d0490b03411031060385405100340d80b00c003110385c3c1d00700c140c101902039014001d002890821403039000e031074070b460a281180c0c0d007241030b203141c546c503084124a859070380002c08001c6401c00011064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 653848228 1250 653846978 653846989
    0x90118060801090206121503100204091404080f0d020904050c0c0d0c0203061302120f0606030d02010204050d120908100903140c0718060e150f0619201506 68
    0x1c2a450000f0303c0b450b140307a80003481500400010840b1002e20f038001034044100040c030681d4865000e8156041d0098403914a0083d5010b03002c6c01c0328181c2001c00c03010001d41c2d104442440b450304885010308005804500c004168000b1a0f0904655024082c4841f50b0383d40e481000d0040005001e62581d079820401c3c00c5c0e05020103035001009209804000c0005038078041403060348a120681c1d06e404c2c0400314400650041107241e83c5144138402c80100880c06000041e50b44c1c0100400c80c05c0300c2d50016400e508030f00340d20807406a01e82180f90140342000003031102611038404100f5040400c04141c94690751342c0340c00249140880c080341c960941e0f906043e04903411601285652400390b1800c1303903080c021942ca0541e40704200269182031400c0505400039403011001c0c210101910780d480c00d081c455070034241c0d9a4034049105070344c492032002d12850030f00300b11891840c031b505608a107400401801e031004000c9040b4001c0c0301d09082c1c0c00000e0042e06105100100d1b03101c00010545007484000e011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 653849478 1250 653848228 653848241
    0x309030913060303020f15010b030a06030f0311061003020325050607050109110901080a02132405090c070b0711010603060606020d0e0f0a0b070f050703031e030204050f01120b090118 80
    0x11b00d4222003048041c141900b48600d0640b1021644141d490f241d4070b225800a1180b5803010b05441000300542d41016840101c050760349003414121101c6480d05c0040c4d008510191000952683c81507200b0001028412a42812400c82c2201800c010350b0320400305002d544810012119650b481c007140003046500e200c40019080c4c1602d035500c05605043c222aa59020070750042d00c1259112289202c480d800d030031140e0603503904415580d0a000040c07244080050f2401014880d4900c01d0000701001c1b090f40654400304c2e085204181c03d03849140055030b1b1801c2c0100030090654807190b000c40490854041d0034010700d1142d006182c1040d03d000d00406213404824550301c04c55032001d00500d103070765030242c034402d0f10107075a182039480c445450304817600445450014810b0245140010a042d00b0045070180560480c00d1944245008042201240720721300911703610503a00c440005035548181c4040c40ea05082920015040d16040001008040240e0042034040041e04594400e11410b00640 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 653850728 1250 653849478 653849503
    0x3c100c05010f023402060d090b0c0f120717040309090c0935011109030f060f0f07050714160e1b0715051521070b030903091306030302 59
    0x11428600300300111300c25400404154810b8075841c005214401c60040300e0903294960060049070384449105855001e03104100041e20301000349800204018811411a00321041302d00c100c0b45840c2008620480005025050078100541c40c1d05148604030b036600c18a010700e000e0f0b11041105842d04035414140c6181a000d4810804074500820070042d0900c4452400401d40441d0740700d611a1904511010441c40f550300ba6543c01d041e00845da450b01e03003008009c42030080d01540c0400c4059000c1c1076071103c0c00d540190242544200040c00310740c5644003540c0201e09817800c0c0f442d041d81a01c401e20140302003003c552541d000084262039034000c021848004040741e44896409140944a21102c0e0440204160240a0001318036080001003840c034680415080c60801540c100741b540c02c0c000d42da0000b0302074082c3c800c000c000322840fa403a112034514040303e40c004140c41418000c100110b43c00181c4051030522043c48401d07019034441d104440f49403c1d1400029205140d410024030703212428011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 653851978 1250 653850728 653850731
    0x92a07030815060c210d02040f080601121e032001050709060201090816051216150e0d21090b04200607060b130f0b0306063c100c05010f 60
    0x4d030b43c2c81801017295454110020300c03100408907100c80040c1d0500c9284c3c0503075000c910000c5c0214203004a20059016205800e04450080e07889032014410800030307001c090807a000da8070100346118441c82c0d8080e9128403900d4061948941480c2c080880c2d007038160f072042aa5141c004100035241d0054000b0001c103003520003403040c080c187d00d40c0e0006100d202c2d02c0c0104461641591010b00404012992002103030407106641d58994402c0001b501003002d100b100e450310075041d10424441e80380150140e034841b0b0800380003500c202c440c054844480300c11b80c810040718940d10f160003030000ba2094080c21401508800da85207064a446c9840f0400c0303008582d08600000300c1d90b940c03a100c0c0001d51b025a070b4480400243e0003020000038600000c800e0100c1c450506140c1000e0307005840d50401035840d0000c0e01255002d480c1d172004c00500382b0403000d100d02d0f40b40c040321108905100b41c03402c0d5a01190901415080c10346082c0204810b0441d04603080b012915007104c410130414240703c3c00b0240c0c03442d02c40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 653853228 1250 653851978 653851987
    0xe0d0b090c0102030913050c0f070b0108011505010e061308060c090910060806010c0c0f060c020f0108010e1f03060603060b030d020d0e0d0312090311010c03050105092a0703081506 79
    0x1c49845112035002c0700287d480c0c0016028041d4081101c004d0112807500503281d100503e400d60000109024240d1154240700840c840360010241c04015940140c441c103010705d00324424044a41c1142080d400e00160340b05d03000804010a11020740115441320055030340e03924a005124401c40050100b1080d220300c1c6504201c4130768865800743c1c00030790074600003498200c98200301ca03070302d130094103ca031032021403c0300056803541040010128038801c1e0703120000d81d80d0001c019a03001000344a8042d12100c403000144401c8080c00040e062a800c10034840700b0141c0300d407110421580b0581040741c070107980c2c4c0e006e00f0143c9401c000703103801079a4038402810000e01d040b82c004c250b0700710020401d0103440c240315003c0415000f901d00008a41c0300301c4040041000504008110003031400038030303880c0e51a110340301c04c505110340902416034001811112894076070039601d0201000c20000310f00400305548a001d0302420b20300041c42494080c2e9504200c40c14211800d40c003a0040f4401107214410810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 653854478 1250 653853228 653853247
    0x303092d0e07110615010e090f06090606040f12030809060103030c0b041a0712111204140c060d0b04110403020117060f19080d0c05030412030e0d0b090c010203 70
    0x2480400e54280001c0781425440e54a801d807680305043c2e03070050090044804002c4841c180711080084030200340c2c4d0703c0f5042d2640d02d05015000700d0030f49540d451400d050000414500304503009640102c4003400c0c039803901e035507660300d4400084150092810710301c00c0c05049c030605a02c54030894115244401411040d40f450340c000c0d040c4101510001c0074170078a04000303828840c07170b12880180ca00c04c25034075400a203000304c3c000300a800d42601c01c40d42c0d1864407079a000c41314840015181ca41c00e54200103459520b03180c0b9007200107001e0b0501c0c044c840c81016030780e40e07003900c408000e4401c00914107400301e1200000320030081030310a25000402502d4040c401080983e902c1040d50004480100e9440000d486440200f40714244ca08409900f142040c400c03618150840801041200c05450a076000b40c050418111003258800c2c0020f0030f668014007051010040284d950500c4038803034204480e41400040101e00e011155140945070369207940104224410140704140030200d003440070710700d04181c13030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 653855728 1250 653854478 653854559
    0x70b0c1f0b010507260408160602011503060c09120b0613020c0c01051308120a02010f020a0806010e030c09152b02191a301305030408100e07061b1713030309 69
    0xdd100c0a000c640e10f0382c40303044050740241040800703825060001c001e0b0100a0900007494001992800d020340051604054525450f03c00d07518201250000f41c00481c07120b40044510340c104614420001448042c00200b03d8002c00131101d05028030903070280c807658010b030041c0c01c44403043c0341c1c81d403164010040401c1c40b503400350340903502c8002400c0c00c0301310074031404c0424a000402d201280e005100385040c07240c1041010640f0a08030342c21104036081030926000200d10400c50050101c42e0310004443c4c2006140c4010041c42c0c584c040305501440982c0d442d4a0b00c0010b06011a168580500058802001c60910041d002a00754000e40d80301d04c8025113804104050010801114020f1058400701000024021940141050b4040f03904050706490103d0080801c001030320000d114502000600c240a101126508524031089c0d1f048082c0b6601c1e40e11882d511148a26800041000f44c458124005c4507200043c50003a80d91b41200c90400054421051040d003a010501003070f40c1d003c2c0e1070a0041e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 653856978 1250 653855728 653855771
    0x2072303031e07020f0111031506070c09051906030c0603050106050901021b040207060906023007050306040b06030a051009060b1b070b0c1f0b01050726040816060201 73
    0xb446901c0e07050f55504034120309000203465030218a5007040c1d100c070141081c0e20040c60051642001003280c5910309400c010f294800e5040050655003160300c200449612035014940c440400f034194118281e000c1080001c0b1041500101e070701d07441d00c01003801002d5052080714090716550810038600704000740042e50343c1180703a45283ca410700d0680c1e4010b013500c0b1074040e1590030382c3c440345c1170103a003441e1f02d0524042c1d0041c04041056001131204202c074000600403680143d85440c07141d400d0383c1c40e4000c084800381d0005010582140d110801c1c01041c2d03d03490020351090700210300c00611424980090590f0706295806000ea060134164180040440f01040f00c2c40710031048024458071769180011424400e941d401a510000c01140c00304c0c4601c00400c6e042054020303885030011002c5e00c18081d808903131401500302c1c00540306000410000b4220b05129554517a81a892a030017491185040207c1e841604800c5550b0818048210040420780c9a800582082d00007440754180048409421000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 653858228 1250 653856978 653857021
    0xc03060d0f02030708032a07120303050c120a09060b011e0c060b030613060501060503041109090f1006090506032118030d0804110d02090105040903020f010207230303 73
    0x201c500050031503404010b007000812802095a48076500e420b085060016904500000c0300e041d0080000d8100001c04d406054444d000c0801550301c107142c500310024000200300c102d141340100501c4550200344000640300f4000008041410136442c40c0040650340000a414184041803112030200200100b081c9040a65407030321034030782d44040c10500050121800e4254160180a042c04014000484170140c56409004180100d1740d0314001100c941c4412180035041070000b908202c1d00c0c1c5031200402e60406140021204c042c0410000303142041c84844010210a55440d4204400d4a803402810b60040d0100c0c081e1521241070307210b01d554039400f013100306078107040051150011005240c01030307000c039809022a41e078450705070b4020780452010759081d640c2c03903002009101340d803900b40e5080049035400780c218200c50340b0308010310000d0103081c0c00c201d06601070040b4a402050b424405440614012071241128001c2d900198481c0c0c1c180c21040170482d0000c00030440b20144032840c840a620 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 653859478 1250 653858228 653858243
    0x1806050907050d1d0610080304214115070c1a0403021e010b101110020f071106030903030106360603060b070b010909230a06050c03060d 60
    0x2042d0540400041070308112507000c036441d030401c009000c3c400144091080040c460b0f402081b40d1101c50300c1d0703980e000342c0c0315004e155039500c00d945050f00c404550b10b4165910620000000c404041d41c40341003900e030b152031001c02c0800d515402c8194000301051810811105d0080d00604040382c00030441c0710070041116062140108081040210700e41c151140c84045400036829420300d440d0094888006071100d1501c2e8200c80c2e10701100800600c505061418018900102e50015060507140c542940c10024900d015244085803580010b000903c4481406207515903a40750703516040c0d00c0d4000c0b058004c0d004d21700901c1005080d160010031071741900c5690500d41c0200051102c109001a10924000a122402e800700788504010070f01000650b851602c0c103008058a94582c5030603400b0307522014010707544110040040800b9580b02c02c40700d074011322445030300c14080c80008442c406060890561680400504002d020f11442102c2d042070200c00c0d46465800d0060008907207076110032000e808503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 653860728 1250 653859478 653859487
    0x30305030a020906071709040501151e050d0e03091c02130504060204030819140a0c06020313052401050d0b06120c040e330708150d060501180605090705 67
    0x42c0d44140075a0003844d4060500e8551b030702d404401840b50b0704035541060150341440e0000c15003a120154181000580c0c1d0341c1c03454a04e04e508420007000402e0720394601071100c200040083c542c11405400c0c01008084003c43d0380f0582401880f1501a20031042240c403085811031400695820f954407040b006501e01c0401d1549980c2840c200070b1040b5800280701076000141452500050030603100c02c80a562581c2c1c6001c002080150360300c2c8079111065001411868401c0c00150031a40a9a00710381d40803c0d1031070f140c80c0780d51002d142c0528a21514107a03182e5003a0b551505565a2046014210550f08100e0302c41180d91212310010011344280d200781003c81c1e1075107032541d0800204210140c010014404600741c0c14040d80c942c100000c08981e82840c00e0a03040d41c01202903000c403449041040b0040240e41c5a1500700c07015003000d01b40c3e2180840b44484243c0594480d040c4464890080744005415450081703161407000403514200b12807410610100300d40c1d903403000855030002c540d0a0442d941c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 653861978 1250 653860728 653860747
    0x50306010c0c0e1e0f0f1f0b1605060c0a0f05030703020702180108010b040e0d11070f030602030709060c0203150c0405032b090f12060e010e06040c0906030305030a02 73
    0xa524190000903408540f0000c11a00c104201500410201c090b21150030320745450795555500346088607500c000101041c04104121102c0d10024200500e51100e4449141c481d00c0021007039000c1c59800710311a100c4d4444000f400340c28001282c0022540000910301040f00ca8003604a0121302c1084007800070203c0060342040c0a07070100c4058580c010030703100004081c290004883c01081c00b6651484d880d02203c00340a04180c0300743c0c050700091600134100d131481058125089022101044110300403c02d001079215030201900d00618890034000da00c0346046807000b01162140d50241d810043c000c00d2810240e1400b01301140c03000c500301c2a1181e55a00d104404031903100c1da62229406119a1541001c074000d0018283e00000140325000e00e44c03021503100b2038400740140928043c4244114040004a4103000c0c413602c500d1244002041c044e151004407421901500c102004640151041008001801c0d044102501c0840d030308000c6d0303e0441d01c00034200e000042400829582c0010b03103060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 653863228 1250 653861978 653861993
    0x1111f0615030c080108161511030a230901050304150b060c0109051005010305030a0f030b0a03110f01020303010b1b0708060c0406030605032b18150909060501050306010c 75
    0x380c8540410001d581ca440c4600500400a07a00003000040c5800000309400801284a941c01542c81c4070b440c21032400c0c20503600d00d1094200100043c481b0202000d40800414000f82210204075214903058603400c6020920205014540020384501004514641d0380c000041da03401030741104c003d440c07160301421408000c00290040f240c1c003c001103291085c00e40c054100d80310081c4640182d407040d0444c1c08046003560000e00009100740c00c20300c801c90a040c86045403140f11044da1030003050354078004001c14581299508207480a01c2c0410000041e0300307114021035007003c2d0a00c000c51440d854114040c2c1c0c4c0e40134038001003691b41480f0044040031402003226a018202e101c00f6a4001e0030701d502049006d80c4a072042e60701003800c2980000f075900d000b0413404025104d0700b100d000d4001180c01403850a2041904c50030601208804600c2100c0c01e0707503510000307403010b51100c150344081c110025120180340e0b44820103489c2460702c00e0040b640e020090303c1e0003100c207007002e0755002c140b4a020707803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 653864478 1250 653863228 653863241
    0x11d070c0b0603160b0d0e010c1b0f06111207020a050d111606050921030f0d02120403051b0f15100902030901050121052107060f090203060601111f 65
    0x2613802030429010501034042401861051080b8208000c030380c60074100103007a96401560031001c01c1c445459003211012008006054503c211001c50011450342d0f107520440b502c40c10907411444010800d501d11031440c2689680006035400104071001650b43c030181d4034207903a14241c0400020022500b0404000c04c100e801207010254603004040c6c4805000b01250000910a481401c40e1001010313114140c082c0b1190700100140034500d42101c080e50155603501c5102d40c0da200c80e070308220a1a95120034101e0034003461007031ba40c90b981d40000c2d40c0e04180b02d0070042404145a00601c5880074020340001d03400c2e00c21100104ea074403466070744803064000c6a027164030030070001d40000100003003801c0650105044c1d0310000d41680132429545111320018095020043c490341c80222150080c2200d01c0e040050b1038041d00c0031602d044099a0350074107036890703c1c01c142840740d00d9200500c211b250500007554080b10078a0710121000d02010500e554940c000410b1450080b0303811900c018006980103907 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 653865728 1250 653864478 653864503
    0x14151809010509060708090d2d08190e030322023303071b020411070b06240a030203130609080d050f060a0b09030f060f011d070c0b0603 60
    0xa00180c54a030019501a003011102d0711124051080080d0016024030601030041c0340d004028041c0c01c4002c90241c45100d80206c2c2405000b5440d140705c00c40a03d82d1603140d400520316a5191140d003014030300d112003030500b09182400d480c2010007440c0400ea001050300d0303015112003990007a18041051500c2911f240d01c0c000ba4000d000c0809400c2c00046c10b014070f8001c04010364421802040c844050400ba01003504e4120009050a14041c3e2900c0007a84900000d40000c0c400100c548201104070b242d90301440040ba080084c003c100140c0d458051b0141c000504c0100c15a103164000c0d1440c2d601c5842440b1141c428107501001042d5114902c450148c6542c1e0b0101041019110508190025410141030444c000b0305040000b41c8180038401c0a82c090103000c0c202040a500340802c48500750861580030390107105240c03556580800411a550103440710740701010316035043c08140a11603001000c503801030310203482402800b5074010b081e1156070390031003803119540d241c10b0002410300c1c580d100f82 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 653866978 1250 653865728 653865769
    0xf050c091b030408210103050607050a0906030506030c090702010c090b0702011e0c060606030b091806061c050715120902030d0503130204110a030605010201110a1812050106050f041415 81
    0x1708028552404198180c0340500c0c11035a20395a00e50040725507110302110f4800290540700e00f00100c2c1e01076040306402c80c10040543e035481d1180d60104d06400400c548000051b9101c2c100e0321030454000e81e401e03001d410703091080342c90a1100e40000e09803103103400d0948841203000c20942041ca01ca003116002d03050344050207005103030f81c460740200a4000781e08050700c2010488082131254001406600c0004024409440e084e5540d0040007424a03d000b2000b420141000e4480d00007081440070101400000803151240d003101c404c010300704110f0040c04c40081d46002c0a20001d030790001381700d0000304034505d00190340342e07070300c03c0030101f01c40312810020341050400c122150b07100e885c0805810f0503c2d807a42c0c2045000d5492004a00b80c0341c5204240326061410049031192a04c5842c83c150404c50303003004014015038949203c3c0d8020b07140036064403141d640301c60600c5245000011042a420110340501120b2034000802c19a130001421060310148800384400b40f0340c032000b10401840c5240b00f034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 653868228 1250 653866978 653867017
    0x1221020d020901090518041101020a05030c0114091209060a090b07050d030e011401140109080d090942050d14070b0f030c090d0c030f050c091b030408 66
    0xc182000e900070b4401d1601048002c04082100d0620880781c0f080960301d800444001e0700d03982c80f011803442823000721504500403102038401240042000704001c5800308000200c0c04803283c81c0500700d200103000780a00b6001202030340d480c2203060041d81d03d00e8008580143e40c9011b003c00a40360300010354049002102d001c1410024024042502c4001d182140c1b0240524011000308508841000031000d8000003081d0040c4410110410920000340040c18680580d17a02c49800c01c2c40c19070342208010024a841400b030024440e107011b0001c1400041c41040c00000c80c07449070140d041024203c01e080106600300c86240205031200c501c0003000041c041c2d02c072070302c40780c14010103040401582040c18400c8d100d000982c00d420070b0480c1c00a6429041141c01e640b2040500d82103580403078180ea6216001260210111312040c140318011481031282d41d03049480ea26186003860011410544111200c4042221141c01803000e1000161107078002e80d600d07034682c60f1a280c80d028030b05a2880f0a050b505 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 653869478 1250 653868228 653868247
    0x30409090b0a0f1104120804090e0d030b18070c02150f3712060803030a1a0114030a150b0c0a1a190b01030e100507030b090103122102 59
    0x1240781d0182809240510207442002c403140c06a54070010101c1001200b080308109201c5001100400c4a1045004602e0556190038803030503100d18800443c040d8210221724078540b50544182d0381e41761000c0e501c00c150109131009880030120000d04600a005440183c01c0c1107688403a030f4494001103800b5016102c1c0b00901e8920f080750050264883c0d250300480d94280b8021300039022020b54014042e0301900d0100602d0219182c0d40c1c0403085541a9407190404036501d1402c2c400745210380e216400c0001c040b1043c20581d034104400c212138506109a0440d42d41c80e11710a04102c07648407543c00000308900750045041900c00040e0f5000301c8111074003140d140306207140032943e9403100e0f01922462501c10651854000c003000c00fa1540c6055444103080c0c81e00030b81d03058010370007102c01418000307994844c095101381010707880b400c0e00c00c2d82a0748a0801480c02d805200c0c00c410707e41c0645030040c1c01e40c11503844a4075101c01c40b135682c00b4015007030691448891840c0c04156030800c8903009640b43c203001d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 653870728 1250 653869478 653869493
    0x4020306061201090e0c04090b1b0d050403050315060a231314040c0504080a02010c06090b07120507031a040218180a0b060c150a020906070c0e150102030d0e03040909 73
    0x1124103245034019425610f815160a01038508455000404001c094860b55000f001012217032100000304ac80c2400703a4600e140c402c2c450030384101e0094452503500c3c6000d00460351044920440284106014030507451810b910200070040042c104020a401d411501c050300b41e00e00440c1c2c558420084080004902d01314090243c00c5080000d4a041c0503082484105591501641c0611607460b88110038050240d0302c42c0d6000350b40d4500a6400282c0f4004a84681000e0a400c032058004105a0303a043c00200072a440b130326500481c680b4003000400155071100b039440b512401810722558020a038042c200114526003042428002c100201c40a52107246000e00201216010a032030310302140404a41400f004880c650075140300506020710700c80200602c7d060f0058450f082459091296100eaa00c03110300400c0035a006049026413503280001d0307454000c0009010043c0001080d2248181d40d13000004ea0350404849140422540003003203c65245000c0ca03403242c0309190801209506010a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 653871978 1250 653870728 653870741
    0xf090506070c1a0301050d030c06060e09010e1218060d110301060c030201060801091104090c0504020d0603052a09070c020306130b06011701060315050d0501062d050402030606120109 80
    0xa10024602c1200100f070041d526001c2441190303000041d4250800009108032010307910184960f200042a0b92070741d59007218160215030020f082c3e0340d01e081e40c0c074000b0410050700308a411072205d814548503004102400d2409051aa14024800403401c00c0800322590040542ca00006440d15141d6a581c50002e09201d025442a40954a007000110b00600c06005041201d42c0017501c514024050109100042030302000035503841071a05400f0401d030303695000910400903920380106441d82076050241c01c1c003d0882e04010b0402d1041c0022120500821403200580310454840c50f2a83e44d43e1011340b0540b0760301000940c540240f10070003402076084c00e10200c0340d602810f424642035a480e4015100c100031409040c10f06103034480100030061180d0015006442004021824142da92022800000a001c801c80e2181d444040030702000004400d8230416404401c04099800501141403070f011445010f550300454002000440f80d071150002c036259a03182c40c0c0c4d45000380d0307556800c0e240203004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 653873228 1250 653871978 653871989
    0x90e071a07030c0b09160807061115010603020c211c0506010e0405060a1e0e0f1005040b0607020d060e010614031e071517061503070f090506070c 64
    0x826421480920089106480740d150b40b60703d61540416498560b80c00902c0002c02245581c4035070514034812020b81d0f2901b900400114005003940307400c0001c0034103c0220458151025800400c4a001461030012820f0440741c0c2c1e420010799504540e91840e06140c8004114907000f0b601080c00200009200001c0080c2c000e020415080034143c207805400380e440a80d91140010406c149240380d81ca407a0f0301158003c04000d08070a101a1380f58844120488503045503080d07030040010401c10840314802ca0741d07100241d803400d9001840c0c4002100b8000101d4010203014980e20400b070355840c1c4844003101c15040d002803ea40008410340703840006429003129440241d400c1510005110041440d501040301e4010090040320900c2208514001e40c18000b203c55131040b03c000113540034034055802c500060568420034010040e81c2000e002c2c0310050f03d010b0044100020f84550180300c041540d0704102189010b8200d40081c44003150110700c2508101c2e0311003000110307041003028802c168022a072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 653874478 1250 653873228 653873249
    0x31c020a0309090b0907032f030f0a090f1b0506030c13150e0411040e09061f060f0e0d05010218130e03070b1305010203010e061207060f05070c090e07 66
    0xa031148008004c0d1050f00c0d070f085401580f00c102103820940a90404500341c00d82c0f08030456848000400034488800e03c2444c030300382c1d09000040c00303081100e1400c0241d1140c1d04030703130500c000e00e106c1d40d0381044c2c422002000761640e21409242c04000c01c41905020003403100501d01503e030705003000440c409074824074a801c0900700c40c00c0001211320076600d81c541040d1041e280d5404405009040c88041c0400d001c08200d1217504201c081100304292001602940c1603d00a01c100c1c40e03c0d030314800c0c9500c90035140d44425002c21004004140d031115050304040715070304e0005592004840031441c0703507040d40c50050081d40089500b032444040c00061303e0320060120b50340d00c10b00745d00c084920102c580f5100100c01c40d400401109021600e94a06590440741100c07940900000e1519598220380007a0014122216030005114543c504026070342c019217100c03c00380140ca403a007a0041c0500322440e084805000c4085000742c14465106245002000100424002c250184042c1c5403951264020100f11a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 653875728 1250 653874478 653874497
    0x120705011503151b050d0b0109081506121c0e011b06020c120c07050402070503070b04050307030e061206010e0d020a0e1b0c12030c1902010608060a02121302031c020a03 74
    0x44000a1480d0441325512514500415925084060020030800c0ca041c001c0c0783d14001405401008100c07000004030f1040c01040c1061000c22400e0000507005000c9580b0241e0314070480c0a090464054221581c1003e002d540a01c0c801617550f98420407003054540110300c942c4041c0800c580040c4583e80c040f5064500703c200318950800030703000f000c0340400d0742d070700c050b4007401b044c01e00364000c080250054080b079040c03140650321015040300c110b078200d6280c5c001250301000c164014102c141040c104464403030428098201c2452030384401000c2604115040c4151101b0307031151103400d1791090700600001070007074451031144801142a5403c109044291002c02e0207002d4a105540c0065800c9014081c101d40c0b548110f4034542001d811681d030f4000400a000c01044c0011110804607582c0d000490520703c3d08246901700b500040030f40301d0030f41c01042031403201040c110009610203100548240e5040950000c245091b40c4031000030404081903001400190b00080c3c0140854401c0e95402082e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 653876978 1250 653875728 653875751
    0x9010f0c05030a052a040914060108130c170601051203090a091a04140f0a0506101b0503030708182a03150c0711060c12070501150315 59
    0x300c0d80000c04440009400b440841d1483d00300303400843d000f20703654040c9443d4a030150858415000308181d04204481e00103810005003d040c003400700b5100b85242803a80510344500081c205680003010220990181071440c0100401e4400e010081c02c080d4003a01500300b140c1d0085641d41c1d1083c01458420402030300f9002038007500004541e51080040d05a96109250201d02c0014000780141c8501c0300038142e44005c0c00c2d0b11540715119500c10141e58442e824100507480389481540900b01e14896824001002403685070036083d0001d14020b45000c1e048620000307a04285c82c00005030040844c0000002d000005030f104140601601842c10801c4100700c13590042603450b2202d540c000580201c0d80c2c40440c0800c0e14450411030104042c00b55070090910400f450080d180849002c042100081010010b000440784260703000902a01c0b4940303001c6030811019038480300380090301e80070000002c035102080029000840c0c5a4030051003500003903100d281c846402420f0f040d81d1540700785810448151f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 653878228 1250 653876978 653876981
    0x50a0215072003070503070318051302071401060b0a050d06091a0325210b0103050313061d10090308031005011202091807020a15020a020f0a05070509060d05030a020609010f 76
    0x184e095105c0700452402240d50b4069980ca000e071700d003102c022111503100003080d40f038148055440b004641c0005a035018a413400050800040e412104c0d2685040014045240350000300e80600b8011b084c01078a0785481c0040e00007802c55071f0002105e440c2080e03260300740080b01c48102d049600d400c40669013201e80a03941c0d00e0124000d0400b0b00e0728450080b03000c102480b1101c0d910216860b100c08005000da03e03d8a4806400000f82d008940560001501e007001e001400318050241105213000c0a008009440040844400d64802e6114100c0700c03540b00300041c000c2c1e040700011684a403155407240350001700e04500a070680320389030110302031b01107502c0c28884502c22180c031104001c5c04250111072205c003e00d034035480101043c09611405d50080085508003010040c0c10148903405695040280c20080c01d00d12074910304080c50340958502c60000d140440c01a0640794142c0d0302c005991355100008054400b0080050a10300000424a100c140d011418030700c54081d10000303104d5100107008050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 653879478 1250 653878228 653878237
    0x30c07050102010c1b1106161506050d05150603012a080606210601030b04020c0703020a05030307152a051b1207030305060d0c0b040303030609050c0a050a0215072003 73
    0x14405ca2004141c400040d04c90844106403440540f007a400e00e07e0300c215041c408070040c482543e91411140c03281c0000400307402208054078054480380c582c103090799280c9540d0300a4030003103a401144100092032644095010300b40ca00d0600c000c40f0413202180d6150300015119660000000c1e07110070000741141010340860314040340406104040d914001841118454050a103d04240e115200800741d0340c2c40d4000b80030f20340c031010054204a491481080031008550780214002e420a100c0b03100030030058046804005105000442c40040d020340055030016902454501180c00306120614036600034054544400028030b101101c500d004800c980e55041c54549034070b5203808004920000388241c200a070002c8000c0c0100b0802c22140c0d40341001c031084c94001070b840400105080050640c1400f640340201210ba01c104014180f03441e5243c03980c4900718a41090000018036806440c1c0300304264041c680c0800d2810b00fa074200481d0081c010340003200741078101c01500d0b560f080c05940c00f0080301d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 653880728 1250 653879478 653879507
    0x4031404051507020a09051f05090705030121050d050408060709030b1b2104120f3c1215051c051c031b030b09010303081008030c07050102010c 63
    0x410381c0703090710b07124485501ca44000c9030031154400d40012020264003d20380203c0c5856900c910345a46166807604d1007060b44d00044c4284024002d010441360000c0c216030646c1c0d05444000304080240c1c0f0194140b00b000a0300500341e1048000e0000c01d035500030040c1050300c000900380c4001c0c1e241c0c2d100442c4d0320702403800041c2007150aa8082502c480c40d0b011011000b1308405003c070f0400035501c1004994110b6400d515417400a0f8000300000c001550380310303c030108040d0421171b986601c00d00e8000c046aa40742c9541c440c20a10f03881103120304000107800070040140c40c40100081a02c00b00c020581170040710301684143c00c080380c214440302000d103032909495014000301c030742c0c20210b05031001c0b0000211080e605030080f80042a01c01000c0e40f042c042c42c001c191000308140a040c40307084480c81c8013503001c0042500d000c00f148c000d0345c0c68124032030449805140052103612100c9404506005580c082c0200c0e110004215405030008507103082260000d0b002001505140c650036035000c024003a21 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 653881978 1250 653880728 653880739
    0x1502030405010f022d07090603050705010806120d080a1107050f120f18060f180f0a050306130516120b0711030304061a0a03150e010c022a180403140405 67
    0x200122031708901501c4643c005070703003101d07500c2c0d40d1440302070100d40c0300e5013080c0c40c81d0304541c6081c409940c010714000e400c1030007501c07032080302e00d03c1040070307500c0d80c0381003401d1700c10011954082101804950400000003c8079024283d4525207440c015644406085480382e00d40243c200104040d5542c0b41610203240c0520042807034080920320f1043d4007040c42241c968022810b20042d220303c44040c01405000c1c40780c41ca4481e01c0c0e0074440800c080712000a0285214201400f0140101d0300c1c0410b040c2c1c1c100d440172606c8030200c812031902504089018181d464000c0ca541400121615002c000c007070884d01441e100c82c02c5440d214011035102041d5081d0902ca03510400210780012407581c48494141504c402610744488544009110400e0940c8143c80e01800448200744802a9115101c0211903030b8000f007150010941020791903040d4454544201c08807910b42c4a401c0544500910118600034140403030a160800781004601081d5010707400118a41c01061a04a1140071101030b124001d21 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 653883228 1250 653881978 653882023
    0x1110901110a0b040302030a270306200a0c17090a0b030901021c0c0f02010c1d0310020301030503030414240c09030a0510152603041502030405010f02 66
    0x640d190038a0160440041c030640e0042e00220701c80c4102c0c140110720907030285654000e80c21005111400030159a018041120404905d80c0c6030901e92000300c9e41e10407004524550211480003140300220740c070b02c2d00580009240f00207250b100c0b1700859828459043c0380c0c1000d10500d1210750a02551070340940003135042400b0f112070755200000e5179008071154001b510b040304000c04d0f0380780b034082502482081600c508032101c0054108000d00020b404a2000700809441160024190502d20980031090721311050f90402d262400d11102040e888444801d65076941d49140880e501c5c2d00c100c0d0103903034200280e0844011000c0202e40207200e94102e1103010a0b40280c40c10a0074500000b82c42900720890401c03120005442c2800560a19030040c2c014128a0030006070503803d540d0481c02440364144079a4040c440441c04d41079000b80a00d0075040e0000c03003080303200074515610840d0455425000304001c0c0c1000180e00000610a80d0307020390381d004200044a4060b640d03080e168400d10f100490355070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 653884478 1250 653883228 653883247
    0x30302061f0f171c0815060307020c0f0402040503030f03150a0303020312070e030a05100515030a110609090a150e06030c040c03150905091506030a1205040e0c090406080111 76
    0x4000794100e03494000d5034019081818486440c070246139400000c9034480c410003070400181809448141001c1d52500c0c690b1070044002500c814407495618421244500c0c8010a0740b5180d0584015100c0a000c89686032080300710042c980d001101d00c0d5000041c0b4511030300080c240b0500e000d040325890313001036080078042421034001044c01401c0d007082010301d400c80c110555040101210360b0340144007810100c409010f041c010340300010012107a0040d0041401910b860010380648140c1d085001444203011190000d4014420204800e501c00188414420090681e900600c4000c45c80d0301010f0740c1580d251001c85030540216280c96043d000802c0c05421800c245c0c0003203080407558503000442c207410440701030f10740000e40c003e5006a0b41c3d4104025900c0c1040000341000e00d0700d50010002c51a052000035a100035036a4010700668400b80e03a001d5050155041d140582003400f172800161a2518121005410546c00144120700380540020111010b100b0090480c140589407450060600d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 653885728 1250 653884478 653884499
    0x2070305160303090602040e090609071d180106080601090f15030b1003020603090a0308090c0306041514150f01090b03010b090d0204091a10050303031b0d06030302061f0f 75
    0x6000d41c01e0503152084e000000f20280700510107015030111109a60402c1561903161000043c6800b200e540000d0040c400504604038a000c80842e1001d1a8000d40d100510b121818000415800d46036003800780104290f84049910382c117991501c0c0c81000700202c0d002182c8180c581200f80b60b8920104140240702003840d56580300d41c0281d54840340100c44d079070303507020601316070088801843c1900940c40d8001015032040c8019045251003006103d103480c2c1c000020384510029000807e1121041002d440210700c3e40c000004003e0410094142417405015655990031705401e81071050008201158440d80143c0d412002d55852040c034a055a0801d070024540e0783c05182ca550b48032081f41c11100041c1e4075401440802886060340c03000050b14144c28100c0d05401901c250420340189030240b0054a00005590f405401414280020390447e00030082d40e01c0342081c150000350425501009140e00016024010141c1d464614560b40340426103802d500220b0213100d0340100c1c07181040011341e151 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 653886978 1250 653885728 653885767
    0x110f1203061c02121f0203090c061b010507120507050c0a03031a2701060503040b040f030e09131205040b0403060e12030a0609060e06010806010f0e12010b0a05030102070305 76
    0x18030030b4101050b0198000941040040311080c00981c481740f0038541002910101d110703441e0351032006500303509095003000c0d01d1b013a00c4d1075401d018600100324680c81c54207510f505980c2254180080040341441a002004c100c040d070040d448085c1060046003a051140b009c035025803a140002d40841516550f08401030071103c5170381550301c50880b0101c0903c1e900c0d0340c0ca00c4408a00c00441180c2d000207400348910012059001c1c0701402814000c1102050000c0b4500d54400d6106091007520700e0180303819203200c01484041900003901c070341081901d10001c03030240500d90040c0c40d203804204401c642190603200718002d41c518907070700740010000a00e0a8001010310443d401c1030322541500902940c41d02c2c0c004840d19031701503403100b00800103015144241d801a04880f01c155019140000010b0b18242024106034100100c11881050092144942c80500c8100400720315410120280c25030103008010301c0b90344a03076440301d000940e601d0140b00b2903107415032580352182050010840b102507040e8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 653888228 1250 653886978 653887009
    0x8011b08160329040c08010b040b070c0f080604050c040605010e130b031204060f0302071e1a190e03040e0f0a0908070b01090506040b1e0609040606110f120306 70
    0x4a6401c0c51048203010380515403035200f072aa0b6603204140c3c075800c100941e281c400704a401d01c40e0020050140c061400c04640544141d4200e06030740348001d00e01017002520990110507480b00c04180031658060105205018ac0e02560880795190f0610003003100715406845418081620300b90304c0100350510b0422130000003065000001d0980700280400d00305040700302010b216220004041c0180d03900704059601c0001c01346400c50800003a80c0d41d1400348030a094808110500744c2c0011010000c1c180400ba004030b944043c03000130360814002c0d440f941603c41e40006002c0d0708106184481d0040001600d0807201811050142c07a140d071184d1502c0300790090321840c103064460002c00302068480005194041c03103003040520b90340c504003113141200c1c0060001445a070401001c40441d41e11740d4045074001501080c5e5030340107209100041d040b80310360b40301c0640103404d010b8002846034220311007072008111501916600100c01c0016503e4040310034440907503040c2030020600c14102400150540607 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 653889478 1250 653888228 653888231
    0x90f09070614070506011403060901110f0d020702030d12060e0f2205070f06110d09030204020d1d0105060f1008070f0909020c0d0f0903020303070f240608011b081603 73
    0x200c40c4c4609003012402d820107541640f0b902e440084504042041d150f04c5034144008001e81500b202d0420b146100c0c42855810f000c1010442010308845681103520841d801001c441561442c2c407006081030601d0140e40d0b895038640b54001910240ca02981440f807031648031044031640c3e4504210465182d821540000200302e404048000b03070301080700c800904100d4140b060600e1604800038540c0b6889007280005170080010310b007699402503611020b40c1c1d4120f40258444160600030030007420b8600c41050100070343c881b2038480c0c0304190311440c00349400361a001d0001c0308540c01e0181c8000d903040030720005480a0009143c0c80e2050090f5146941c46141040c401070382c408030740782079800c201760b08080c50b00660646d44030303181c11040c0304e200c450080c01d1096800d0b1640c0c0000b0b40b01d00810070090000c866109000c420013040300031482d40749d454115130f024400801c558010040c0403130b020309616507180c02c0085090400c0290044560721450f07542c0c11150b034a01c000301e020401406914000e15 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 653890728 1250 653889478 653889487
    0x6050f0607110a091413020d030c03030b040f060509010801022b0908030406020d060608090a0b1b0a17060117150429010210151205030d050f06090f09070614 69
    0x1070f500c407110b010040c501d041000c1400d1400c4220801c84450140005a600014115820058a403540184111074050505917400001400c0550290180001507a8007a241c20b80341c200c2200039030312000c161401503441c0e503807503030300c4501c018201c0c03042441c040403010003410150711000c060007400c1c4030311201040101e5a454190390304507058006a5040301d05503000302c2c0c0403100900c10301c9514020040c03440c006445040000c403482e00d5111323107440a03201004440024403414040807007003410084205401c0c0c2c0c1c800380100020002c0c0c0c000754491902d49110004500305611070f64652401e030042004080080d1502440c00c0d145407409003800750865185d0b400b500400c400000404036642c800e652408e0a484008002810141c000520500c400c0c60036600c90010a8000d0044040da82140180d0005007880e0400307525500a2001484869050030104000c03c0a0241024060201a40e10504a840d810f1803030707006142c100c80c54002e65004039000c10000d0721410b41181004900070a15203003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 653891978 1250 653890728 653890763
    0x40c020f06130b400807080903010f0515010302070203010b1305010e0c03091207020d020409110301060e0c04050f0d0611040501030f0903020d0f03140108030a0e0a03170d0e1b0a0906050f0607 84
    0x1b5080b500c010b0350b81c407001103505500c03810280240401d41d582e000040186107090b0300b03820282d030a04584d950405a01084540440d11300354017281c1c4100c1c008102c000c0d54000b2014070782c090402402100652030300c070004a43c82c09542c8054901843c0d4030380250004440c06a141c0290790000e81050b82d20403011000000962150303c2100e9003103001d04409082c0890b12400c0c5406c1d50496404800e080b22000c041144940d0b0210a4a080d03e1084601e421300324080000074080a02c020005003c8038640403c60344c00b100b00000400490b00d0a881c1401198595101142100e40702c2d14094050f07080041d8000303009100d210b4500c60801c1900f000120b4030280c00710f0b441c07460026044444594800110401c259070001200d0f6021802222058192801c583e28250261b18001c076000c545100845c41e0070080342d05422000c0301c0c440b00c078211010b50200d8244003945229112004c2d008041940c00455101ca0307a02414094502c05003402d0400c1161f02e05000d280d5010780415266000d009910050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 653893228 1250 653891978 653891993
    0x190f060b0706150b0406080408091813020f061c0b040f0903020606180c0703080402363306070804030b01062a02040c020f06130b40 58
    0x281507028060000d0315500000030f40c03c40141680041c01201c01c00e1104018103a031240211f94481e03801580c4a07100c02111011800401078600006502c45c48101002445051110744405407402114180c000450100074050300740f182522885003020712540c2c504012030160801b030307401803001e4000907401d200050901c0854400f981d04030010303000001800f601d85051014203250070b020341d903016000d0800680e601d210f03114000c00241813041000008065655404101c00d1a611100340030114070007500f101038005603030314090b041051144021503080d00c40c40340b245240328500d003078200d0f0141440c110300c11006401c5030740540c402410006800011440c03409000114401c0c1008203c0b5410198003030310444103d130013582810f82c01360b01c148084c2c0034170016482c45901501c4c00180c2c4400c0740012405d0621402c48441a03107e40420f10118282824641540600694510b01c0a031034030b401e0f10000114005010315855109441410712441e1110000e0824491004104050031150354100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 653894478 1250 653893228 653893237
    0x31317181c021c0b06040501050a1701022122020f1507120503060a06111b18160f08090d050a05071b030210050a0c14030c2a09190f060b 60
    0x1008036020020410402130300c00c59261700004211802d01003903050130007107200802039204001c0240c440f00b0301ca6500c400d0a504407a2041c4031907040e1410101c5031011100e042d04251040980802c2c4141e180f000b51160301100d040e140d500170030703000111665904000c41161400320045c1121000c0011900103070b000c160312140f000300c81d210551030b403602008011501190340c0c0a8000d0006640e85524069408103198214413034030550b040140e0381240c0480c00080d00e0280c800c00c00d810354000d2007606a61244d2086510300c80355621444421060821582e06d0015650b0700c090368800c40542030040d0007100034112054482c6013090400d001c980710040d9404468001c4901143c0c070000078019401c00707401c0b0450700020350406519102000900074000300101d6805400f00c5800000c1c14034940060049031005a80c100c203c4c0d005551602c510429581080c607200401c0560301c1c027901460030b10084840c481c1800700d030801c4118040040d0321000d4024040700c058025543c86d40403c54890940241 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 653895728 1250 653894478 653894509
    0x2c0106120609030f21020f0c0a150609061d18300c030307080601110a080d0b0919050c0d0c021f06050a06050c0a050102031317181c02 59
    0x45480002c0c0e0401800005220406038108040c07a89625088002e0384416404808030805c0107a41d501c0304003071a03899010f00481280746029115500702481014540c4108510744070004000c0b00f81d4880414003143d0300c41c841d0f030340480030315031601c1946540ca54241d58040318110113600c9500c1410109810301524000540c03502d140314505400000c8164521a482e100b0300c1d01c003030700d45401080d0f06583e0340801840b034010800703c480040ca85074480c3c1407080042801034111080d00c005454400c03819000308412000f10740c03030494800384529040d031000740251007410420528070128079816014000081c00d1442c0c084042000200203000c9104502c0c4000f4154042c2003d080e01c0f034a079400c11880c0440c80e080c5181003800038031403560340c140c44404445680c00c004e80d81c0c5450702c82e601d0400c000d080d406080b9510100401c0300c181403245039480c02c3c1d403140300d480d24003500840b40c1b6116805a80c0711445c11306107103448200c4a003041c50100303220b800844228142002030390300194540c0b102d05800f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 653896978 1250 653895728 653895731
    0x703020910090c14040329070207060e060909040f060207050a08030603010510050f0f2d0307061b0f02120d1e03090206072405090703020f042c01061206 67
    0x204240c00721807040394114045481d0040f031300401c0342c44107002da0260b40801b0f09008082014500340450744041c21006c00c0e85807540b007002e8030708181e002e0348400e040c1c46400042a88241402e026240080c111580040001e110380c203183c440c3c0d2100c0d509034075001d000301c54a07a8200401700200b4810020308409510554501e81e8910380001494291080a0500d401030b5215040a200702d980d03090000120750f10550346004400f883d08009503010508801c18001c14070001c40c241c004001c109501005260182c0071510b134107513203000845483da4018148060a0443d0070610000f800c401c00008095000034411508407020154003401d1190a010050200301d14550648001c4000d0480c4c00ba0721149007810054441c407900440c190780728496008110010070b0384181c002500c82411211140700312a01000b003840c110101942c0c4400720300051744140602c00483c4441e00d814000c101c0991107059980c1c184044440c140000480400c0312040d5954855501142d0000040da03941200c0c0e005440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 653898228 1250 653896978 653897011
    0x603182802010e01050705120c1002130f0503280c030b07020a110d0506040b0903040e0708010503010510120615051c0605060907082202220501060203030601090506070507030209 78
    0x2410303c03a5420041c82c1400018418040424000700d01d4015403c00b90050036038585011a4407400c1100c40000c1c0005a480800c1c003064500000031901e080c0c44120141c040d0882e100c008056031603080d0f04034040e6104031788000c0c0c10002c01c40d0300d06680c075603c2080f41d15070080e100d035100c01c101001294a500141d10041e00174051044510803039003004011340c0d0700000440b131501c4d0640c0790b41d00104003402205031100421f80c04a000c1003107900078030000d1210141f5040401d4020410074081c440c061203582408040342010407080e00b080221041c918460007010001d036201c0000c0d0500c801c0c2105c00d01074030840060152110713002c039041c2c1d10700c00e0004100c012480c60403004480000e00700c1801050710700100700107140c1002038260040d03041260034110166a50900c0d00c3c10341032850007504110003410092980352644112051404269403d0040345c0e00c03602c0c101d03501c0c04100d03800ca0009d011140100801c0c14550010507100d4000c0c3c0550f00095102d80100382c0e00c85042c1d5511107030525411 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 653899478 1250 653898228 653898233
    0x1303142701120b06070b061201020c06070e1e090601020708010f0b13140c07050a061b12050402010807120e06010b09031c0806151e220506031828 64
    0x38034801505000b01010000c020410012804902920030006c05c21590200450059500e065481000110003c000e40d07441c00313214900d5440701425142c007004103040c840560245c1c50480c2c0030a803070004a451001c4446450b030700f0414515800b51940d41540105100459a01400e002e001d10607500c07a02d0100710f044100050160074080d6015403200a444c00300e102d0301c03c90703080002541201c1c01e0340740152035076407906000e0304000349100d00904e01c80c6444940343c1c40480e00000c1141c0c41c1050381f42c070701540368141000b20a0380c1c2e003110000d000a242400064842c1c0c007402c02c07503d96403144000012007180b44004545131400a03000f4180c1058086a4640c8500c5d0400c0300100c0300850342c1c500410020740b1500602680d60280c6128442c055125442480b40c0c01d1340140c13500e40325a801034401500c002c240e4004507274051400034444d1031004041d00c43d001f103060605000c590b4090402807542d640ca5900381e0500b4541228035100b40104910007888100d0300312480e060300d80c071880a6108070802d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 653900728 1250 653899478 653899487
    0x2010c1428120c0201090b120109140603120c030405220e070e0109020f0904050a0603020f0604062c0d1202010b1c060b0102100f05041a1303142701 65
    0x74111044800350018855000880311950401c056506003410103a07190a8401650710003100e0700550542400030800c481c40c908401d40d040e0488840100401c02d251018032001c82d9080c01301c0318690142c0c402e40b0140aa0303101003004024041e41001a20b046c00d85403000654a141a910800800100b1091401150440d44269030440d1000070051204900d00200ca65204805115504041c0e41c007045150b040d5031142c089070f409140082040086d840e1480e0807a0040c0981d0109038090024003451140d03a05200e01250103035040303510742030b003258100441e003c154841401ca9100300c414084250043c0d0711120f00c1d05a172944900c41020301054443c0b4002e08480d0562010347c411a00d034050561844410b5800035a031941011000c0f0326500c0000060740f901d00d0341d03580c0809242c6001ca00c0303442c81603a540a940114481d03d0503102080d203002150b9001241a6181d002e4501c91a81c19400240502c41160784441c01030009801c21080c1c2c540c201340c051444507128282c00e041d140d080701e0340da0301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 653901978 1250 653900728 653900773
    0x20f0a02010501170616080705041d070e030601120b040503040306020c030712090501121d071502060c04050a150909050a020c01150807150c0503040603060f0b160f02010c14 76
    0x48400174100c17032404201c0e502c00480040c01030000d024125002c104408e00ca90202c4024102c4411280d5404100c84201040301d82c049030210000f840ba83c401e0746c000e141c0030440d9412500c01d22401b003c40300441e1030341d0075000405802107a191000308800030001d0b5842c00581140200301002d1905d44400703051400e040c1c0c1300070343d00308104442401c0c180001e0ba0480504a00328102d243c0010301404003c0c1c0300c202c40010f402d0104024800ca10740050307410300c2c07030a81e0350450140383e00341d6826403140c4128110038042c038002c841d030040080d030080c85404500140c0024007866440c04484480c1d9445c1c5c290200d481c20340c0c49001c03141d00050762000e150003d02516400e1555403185400c26440c0020b02600c641280c0200020800c81078803440d180b0340725400002010b41c1241c00e50381d4a9689000250081055105105c59080380000008828903101c0a558160390743c0030341c4950b4104240e50701d65088e400f6400880c1030010182d05000803400100c0040346400d8000014560304003581241c2451281 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 653903228 1250 653901978 653902019
    0x105090c090c070b0a0203040204140f090d020c0a0b0a1412040b15130b12240c0406050405010804021507050105250203071b0b07060c08010b04141003020f0a02010501 73
    0x403c14600000c03020b180e4907074004d4070b00c0b00040c2c5a4541c1e00c002800340115035125102e0502e01e07004d1204201403024070728040d2070700900310f802030404444103903115020151050b901400d14203080080304500c2c0d004040c030044a1502d40c0010403c1c444051054101c01072036a42d036051036040108206286284580280c00d4040380442c48a5000006140804030407010707060f5a10713076a10035181d454560080c03068031289429140d091248500310841d41091072000d00351a50520080340f0180250022581580c02940e00d0303038176190400006445401c4043c000300c3e0000b840c0c00a100304c41c80b015000e050624490800071981d0f040682164140b02c181107901031201d200100808413060f00002120900741e400a100070741c1714140410680c504010350301c4040c542000084020800c1580c0e8483c111320740481e15040304507625100d80504a00490080b40819050b141c0f00d810f4a15100c882d01d590741e00c917031501500c1c005000c1d2440c0d4084e00003180140140c2c0d150700060020b12300d0603c07402180c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 653904478 1250 653903228 653903251
    0x30d060902040b0d2c1f0b03061f0b0d020d1506050403110a05060307050309011b0804030e19061d180105011b06062403090b060609030a050105090c09 66
    0x906040300e082081c400c030580c4204081d591011801c146000301702c40404c0d46103d0f00748006910781e581441c0e84410500940e06451036107921643c88502041c07203a070441c1c1e14050021721440e40c84590302c072600f0901c8408a0010198440c0c000b03549500c02d402001c0ca59165032000d40c84140342031616040d10016000410b8100c002c85060000310f0344402a102100d810845504036520503901041e60800320341c2010780c00100000c1000211504000114001d01448000b00300d181c02014a41e0701c02200c00d007120001440d01702c085070103e80b00300c41801501600610401c100c074030594000110507060307400100444e03007120007904120003140c40c41070f01c0c03807064452404005220800d440d91420500645040c484015440e0300c1c03021003080300c4140c4960040041244a0300e400e00d4070600004041e060f20300c1d02d2034402035105180309000e020040b961250350b00c481912400201f2001e50800c640d070383e4061084010080104001340180e9002c0c1035100b025016400300c54092000f0410010328011008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 653905728 1250 653904478 653904487
    0x605090106061e0c0209130c0e0103152c0f0d0806060a050f1b070306061d04110d020301050c030907050a060903060b0a0506280c020a0302101709030d060902 69
    0x3250410f011403d03600c01501041c0f0704044603103041d035180400603c00394100750718404010001e020403021540b241d0281090f0110f2564402041c25611000d000040070100c01d000e4408802d03a803500004400001c81c1400c5500c2c1c140d07039040b20f132101403442404043d9401440c030b460107034034148034406400c05a880c085540745000f41c04219203104500310a0100310b03001a100401107a00410380d40011241004003d090404c01c1040303070342d10342500059031002c0c50804009403401c410f100c00b00d03c4410112511170281d80d5a1140341c500d04030200c0071608540714203040e0005a4081c42071b540b003020201610b41c1c5a0418001c020701d0140c0b41c1e0065809a41c40500c180040c58001d121300c000c07a640102c0220b03060070001d0100340002d10541c00950000c102048158405a0306841103c01c1c85002944110076068034008944450490344003940206401e201840542020800394021001a040030103e5000d501c0d0342c0084d41d0b200b26180c40c60307070b080482c1000c59501e040c06948020421080c040d81071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 653906978 1250 653905728 653905739
    0x40609051005150a0f170c03070305030703080c0301180e01060504020f1317060114010201021306021524011b021206100605130b0703020c0303180901150f0c06090215070605090106 79
    0x940054003501000c0180c690115180301400c100490387d030040902a02c2315696030b442c00030799030340109800f00c1c0070414090002d5100940f14054a040307660b2510a0030154030080000002000200240201d5549901e8013140ca52214002403080112a13000c0590300d1000a4240360b000c09142c10010044a60307506030b008414000804d141915402c5240d01d00032600500107078020700c2800d10100308404404000100315802103164001c06090010145c526a2921a207000300346054070800c1c160014950340b84021b51141c56900030303a40800603e0000b0076290340004600d4554103050441c140d100004101d13840c3c0074602e201c8020301765418212b051411001e902c6a20344098041c0114490010440405043c4204a00e000c48400030702940da0b180060340f240701701000f22541160084060b8000050544898854080c42c0074a96070741c5e41c3d0400200d001100c000740108410783e41c0070b864006110250f07941e102c0d0f4401004880c404940e5401c4a0719044040e1240180f085200744d1400d1401c101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 653908228 1250 653906978 653906999
    0x20a0905090907080d1b02190303032d0c0c14010b03070e06030a14150a0e011a0604030f080408030a090306051e0705090111011a01091a0909040609051005150a 70
    0xc09805c0c1c10000c190400249402031110745000000c4d51043e04000c00b04440080d0164002c181da000b560188800039007400c0010340000c0d8401c2200360018000d504008110080c0d001800e50101413518000140e80c940702c121450280980b40ea10f965075038526125a0b26003040588001d04503211100d1042c600480029203600c10040054560402c4580c0301c06010340a0040301015040d0a00d90341c5641040e141e00c1b0700900c030f074650b440b0242d0f1a0072512102d910030b8900c0394059030801801a46040d086aa0310800400150700480703c40105010101d9482c5052000d0115620301c1c0c0e460102c03162a50400d8015100301810007203d1b1400780010410900d402c8040395800056403c10395621081d00c00101c407201e81c41f2007400301079440e11035001d84800f01101e4400401400341d84951a0725113030000700030150b80c002c0d00d511900d031f002c01070444c00781000c11003140d0040c0500f0300060700068540b80c19013005980884030000c256200300708141c0484034849131408a0b0181e511404140c00c004400a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 653909478 1250 653908228 653908243
    0xf0608070c0209180a030e04050606070f1502160501050907060804112e020601050a05090c0a0305070e0409060c09090621020607120504240e040f0f020a090509090708 73
    0x90046103854001385420580e042d0822840071110200d809a445506000f0714184c01202c070303907102e98149004a0b07010300d06103040d40d005581187e04c000d4061001d030f13142e11070489800c80c2202c90390b070240149607800070141e8280d001c550141001040507e040244182003c100360065810b001e40b14080c0000b0507400400b411991318141d400707510740390001c2440f110390640f0368013410307035034015039824032199a0100b8614100c9009456040c1129100c00800490501c103e82c00c80d00303031078103000049803203100b5013001c1d03000840b074146094241d14180100e004e45410f20015111203440f1100e109040307501103141d800034427220508002490030001c0710442c030100002c81100c441807010b603100070b6540710390407600a00c0d807115100b07080358850f010140c104c0d001407040054500d07403246100300d20025007e40058000203699009072900a40d803c010043c801080d480c90340c541c0e01c3c122544070704994401440042c1d031603120307600101d01c0c2004109444c400200000c0168000400130009140c0000d140f5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 653910728 1250 653909478 653909483
    0x303071a0907230301061a07020301050a0c0c021e0d110108061504050112150305010605130e060103021c06050a020405120a0b0a020705120a030510060c05070b0f1e040f0608070c 78
    0x15402c50f070707003000001d0140c250342c1c211a6100424035651b00800702c001d00107011561099000740065511060118102c0380300c0303880341c0081440461008010f00d0038038880c49003000c0f0701d104100f01d0509080803c030902400c6070100e90041801005d200c1c7c40d038216a02e03a520903800ca803c0c3c04420040c0e414040e09010f81d1086e03a06000c116044e040150f5a250000c0d01c2c03850140b40b400c40d070260b4030706000b4060845440303014050040040700103000c030f600d400b480e40082102001003d0503483d503400e0048480010312080c8084106a600c000040c0700c40c041d8500030080150301503111810002009240d02112030600b90540c4042c00140018420403031049d440440c110005889582c103040090500b031640ea0401c811901c0001c5038a06c032034040d030010340500d40c00c0d07452240310b03601d1341016582801c02220250066002c0101000030703c00c490005c280c2040404146403c0420041e10000750b0841100850f11591020605100011041111000804107803a11a6181c2090340e0080d04005200502 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 653911978 1250 653910728 653910779
    0x8060402100f020703021507060b240a2c0108010518130303020f07050a0b0a0e0312150a031406102301030b0901030f060e0d0e041a0303071a0907 64
    0x340020354021302220004580240c80d440402e0783e4030750612170550011500321403a514042c507041460070070044900408814407040d511388001100500f106400c00150802040380044111440f0300e1081180d00125000310110000e86041500144c00c240050b0405405000e80d40d003400402d0400c0da0035079800040b030400a503805000c60a0440207072096000308038039034000140380d401300480003e5481a03103006201001c42d640b078071100340381951345440580f401c0760710602c941c003005d40050401e00c3d04411541629584151501d022400d00000b036401550303403618034064255408003d12102d640440307044400d408182c10000701c5002c601d40d0154402801002e210341e410142d0103a03010428011f002001884107607540d04c0d1004c100c0c8109074040b41c2003402d1400c440038101000400c81c246054540b100c07141d8681520510009102d44041041c580c1031040c04002c0d030b6103052000303283c01402108007609010404600a10800000c0c01e809000d0b440f0304000c0042c039401d95410343c41004450031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 653913228 1250 653911978 653911997
    0x50309030706180611030106090803121512060108030c01151d1b0f090f01080403050409090503040b04080303040b0f0402031e031314040f140c071412030403090806040210 75
    0x100a140002e07070710300a0013145016484264003c0000103941298066941c1d02e400300e860310302494990240741d200030505036100010030484405649100745109002c1d04584080c20003407206450042d00ba8442512a00005900c0403c0325007801406201c01e00000068075071480c016004083c4079400348440c0c0d4603071501000c0391542c4001c0c1d030542000340d80c0400d400c0d141d111903164242541c1c41500d4043c8500802c0d01c3e03c0740154080e81d011445640c040e192241032030700d4904003502038810088200c2c1c1d640801c21010661100e0800500301500546000b10b441e0300c2c05103810302801401402200410410034100801a41c0c0060340e0902c4d01c2c50340440a0340c0d0038162000602d940550307120580c5440000b9004550b60040714a00003200e10200d8051180020351401c001c200c3e8540c2d060441c40d1625600040e0f0340d11034881c001c0910500c0340c00007441001846103601c0c1082c0180d00349410180c000014481859440010b40c0701908160300a400507081580c0000c0001c08580d80c00d60500034440e5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 653914478 1250 653913228 653913251
    0x5040b34030f020111090307172a0109051f1803150c030e0f06041b05030d0e0102101e090503090603011d01050a080a12030e0a052407021506030c1c12050309030706 72
    0x30007114440e004c00f2b0082000c24801500c420020442c1c42c0890000f019107100040034642840750311001f0307500e81068003011440140403260394200d16208201880f42d684c4c00000126a0120303424109403401000910000c00d04006098601406080c09103510810714000c841d007012525135001603200075100c1c414580344662044402003a0f0119516009008012100c50340003d030510b07141000341d0944150103d0402824119102401081c05540100609006189495100c1003845004104072403c14440100254940d4001d804c052401030700010000d0f80360144502c920b0140034100ea601c0803044c01c0c5003105a4490001101402c07511140c03082c010000d0190b0f2190266540843c1030391040c00c0715040c016640d051090304684100a03508032501481401529503018541c51341c0a080491200c16110800b10009070243c0c5e814010003000220b90390b00d46d00c0a07020041e00752200c01a44030981400410140c109158906128082040051950000c4103d60544d980090002017405545 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 653915728 1250 653914478 653914483
    0x8030a0516021f060b0301090c080604150614071e0512040515030604140115120c05030115090806041104050a05061309050312070801080d05040b34030f02011109030717 74
    0x640c09a0004c45c000000820504182d0304900e40818040c1c84480d86503d811050200711129421244000071248000b480098840e05100d150310104580c081e043c0f034002d031110080e807002103042c050585180074071402000028030100e0744010000c0009810300c2d1500c40800c0707035490380000c3d109400a000000034020b54880d4000052a010350504140d40c0d0b03181e001103019803d508004901060000e0a000302c070503014014110003d00d160b41d060700710703440d00d02c403951040d2200307054100740442380c01c0101e002c03e4100311082c4100d0042a140c120020381c0c0007400129607025020314000ca08100c10042c41c0d0701c65841d40f50b81407004140005500000b41800703821806048410b0386580e0b008000e0201c81c640c0815094166030024056070040041982c060354944903921070034507041c5092150f040080d02c000c0101c8103640701030060460303d08265645280900480e030b412000710342240c00a2420781d9092080c014242e5900003241d151640038000a66a202e01e4450a803949081440814444405 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 653916978 1250 653915728 653915741
    0x1172a2103040f231009030b10050103050106030e070b0913110c0f030304053a0818010b010207090f1503080d0b060304031d12030708030a0516021f 65
    0xe8509011804400d816099181e6006101d00308903200c0b0900042444118110094413541110003c10741c01e4502d03000b4010004c401c2d00130301c000d00c0840900080403c0c0c2e101da03100d1003010742001d200142c0d424000054210358060f00040308151620018810700a0001243d1064402c441d4140e0703200c00960000030f01c10050b080501c103440c0e0908080121401d9003401030805c1401c60810b4a0b0508100e401d020f075640800c440240ca42d5205480360f907060760791400d0380030b0700c103189000440071820180030400d43c0d060444400c0300040c45000410802121150342c64400701e102e00700030702ca01036410300001e540d00d9460007400d158076541d890701c14030304503d0741c0008009443e443c4508031060340e030306040c0170b5a0001980c008105003442204203c0e85400c0c0c0469204035450f0700e8080e040240d640ca50440754401255440d00400c1c1622400120a4204050b1036154810b03005180d503850b0281050f800e0325005021070032407103d8000e141501c2900400c0414918402d205c82410981e8420150f0001c4c140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 653918228 1250 653916978 653917009
    0x150c0f0a030608010b01110703080c0114090c0301050a051608090c100203250c140102100e010608011107050a081810030608011d0309210f0601172a 65
    0xc610401a070103412200850340300d0402004400c1c07041c00152000305d000741000b07207a600403542c1400000e17a15405403141c80805000092182c400c42107c5402600607200c0c0181d603070040481d14900c0c0781c01d01520380c1c0305075841c40c103008500313091000720494220450310005108000000554800c010042c050202c035000309000c85000380994040d450703078131041c03002d50020310110000b003000521001c03202102d6880b01400c040b00d46086200504103180c840440e0440c0218140107003c0700e8140164050741702c07035000004840e0701c0c01c6a21401c46c1c400b900c80c0181000c0c14454440885e50104820700c0c140c0d082521140e4170301079003c00d1f034140591881030917800881a1086481c40d070381584010191407040c1c00800c00710880061340280d50300071000c0031005074002c102d1740c4c07264100b50b8041d4230142e40c2d44020b4400d8807007003034541e402c081c880c0301e40d040d07268810001004080414180744100448080251281002c4522820240304012008045061031905d1100c65500c41c0d00030042e002c807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 653919478 1250 653918228 653918257
    0xa20011725080601050d0e030c06012301021209010f0915080a0c020303250306120602070c060f12051003120e0f03120306090402060705030f1903050702150c 69
    0xd0904194009107018500100c000c02030000315880c018040c00490380904816103940b4108001d210401d8080c0070f407004486c060740000d00c0460034a0030708001150292054803481800d25880347c04046035011035031011411903100014041c00b0060b04c0d0b00f196080c520070300c4e04640a00c0c2d4000103580f01ea40701c0c0e12842c2400400a45c010345294000c0003580148a50340060040443c030403001c03640ca00040ea845155521040000740c00c10070000b00e0340c403594030305040200c0c40356581c0018030b00303d9802d0241071f504650001064020030401d9120000070340068100b0785001d01c00d611b002010b02c6c000d042202001a40c82c004280c4840345e800a40f002035074009210714608000b9034005000305190281d05020300d00c0c848107000c442c40c020aa440096401d03070740480c2950f6802d010480781d07a20180040c0c1e007090007004042c0210b1000e2004004120280c0d4a83d80c1d03840406040c0001b1804842020040528240510070200d5010812480e508900c0e00c180384103440d840c5100501d40301d40050749002c41c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 653920728 1250 653919478 653919481
    0x90106121407060914010c030311071514041a130204110c0607050c120d09120503041a0f0c0304300908010905030a0c060605030303010e010302040e0a200117 69
    0x120001915007840c584490076103407801d5841200b61141c0119004502c50404616801e01740c0303505c00c0e4001d42401e80039190204490780030072901100c3c3d9000d0750f01902c0780c1201074481e000c05030315030050610118210295103180d1510f520750100300300ba0132044460a0b0190780202c0c1d034585402e031214142d40d4000308200308280310000040d481d5031041c0580d80c814011000040c98540c01801900da003400600d01808107420174080c000714507403118945000e400d603528195004207000900d501100308250311915a0780c14a824450f10700c503001005002086000d80030001c0d90300c00d54118541107064400600d40781c2c0c40f61725110b03000315611101400d030800f002c0302c1390580012100050b91448010340350030425944031a0b0a0703080e105000303c060207540c01003001d450902c1c0302d403030710342501809040002105a101e100090441d0310a80c002102d1200d01c3c0014401c0d0315044c03003011110a0840002c010a0781c140c1d540f2030140c05450b111407640b44090a0712a20380e4084c05a003a846e11002001c1c80300c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 653921978 1250 653920728 653920733
    0xc0403140a020616050f010603123e0f0a110909030919050a0801020702060415121b030507050a020604120c15020408010b060403030801031b090c110c0303040f05060309010612 77
    0x949805044c2540c3e1881900c3d042801e03604184036040940e60420501050b40400780005c0d180c14400c0c0c0e49000140510070000c44011108010039480d03800d0780c0302080003040200c50303214985241c1c5910390200303801048a6400042d400300f802c00040109851f40d5896903a031400c800d00314003c03074020700d030400c410010700e043d40881141a0740c1510070442c0e40b0301e00300361200900d43c200e000d03420f4025006101000140320000c0b000c00e020400d00308a1512101c00c200b090300307170003d48400080700c26440c2104407440320310035054052035504c001d07a840c010b42004c605080007592044040c0002c0e184400b0103907980d8409114a0f01c200060742c10540007580405007200b041c000351700c6441100b145500c1d1100164080c50070fa01220100c94050395a9041c0d41d003107403681410301d00e40c0c2041140c44645aa000545500c090003040c4900806481e65041242d11a8040e8104030310103000034441e402c204401d110108101c0880b900f526400d03070700c1c192030b83c3da01c07907825004280c0e5070081505110410051001c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 653923228 1250 653921978 653922007
    0xe0609070509032d01020901082215021222170c03040f030b01060306030503070b0606120703090c05151c09050703080a1d010c03031515090303020f060c0403140a0206 73
    0x4800359a001482d42c43c851321240326080780104d10860f400101082c01050041800c00305c44218a10403c50003541c15450759181c0440b8070707a000b04503c1f41074020540280801301c5c001d686501007005c0480e40464060b0340300c602200d40c89654001d144600c84070b10b800c52640b001c810f039103040e030341c0c401140c0e640e0391250121190300d21280b0044600340100c200103d60300e4801e00172542101e50013030040d402c26070300ba03480016444004143c0340d00300b1014040b40f80c090300000341060080071541c4000801d190303d400c10a854443c1c6811450185c0898250b0304548801c079412501440c13200b441d00c1c40101c5035080c444000c2c1071900c03409000f40c070407650040180410790300100080f030740e40e8590110314107040c0c1d0282c8501c405d401c0218041340b840c0e03550b400868065004206c3e4007524070341d2164810b445800003054006540c00c02c100062000c0400c0c030401d60100040b000c92095040100150303d03241440904a00c103030b01006158010101c0303104080801008002e00443d80101743c1c540345c6072082c14886 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 653924478 1250 653923228 653923273
    0x1502030c0106050f15030723030105010813050c100e0904080919030c0b090d060507080703110903072d330909020913110705070f0e060907050903 64
    0x30003035190060010380d0385801903c3d25102c44014000054407030b9528440c0c102d68000502101c24031141034a50301e198007001d41c041c1c1000d45803003d6503440354102400101041030042070051a4000410b00754003107480040e54500901d4112924003050f041c44804035481e07800754010580120007201480b08000c10701010705000d074001e442511544003000010301e500139881c4009041034652410600c00e0014440040c089940d01900c5407441781d1403a650301d8200c0f02c0845070800002c08a800340040f640d418065609001d038100c0d415410007056500081d150080c0340300700d040303403100782c8018452940d88240120529608403050402e4a543d00303004400a200070000d482c2001240301e000b504090b101203090822200d80d81d50807450340c2040c014074000d501104080354084a0b030032800102504500403440211113803920552510014542940380c01002d800050b030030800040144000741000b030314154803040485110610b61211582030b14244619000380350035010700110740460440340303503a48 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 653925728 1250 653924478 653924497
    0x616030809030a080c1e120105040605040209180a110a030501151d040911030f07090b0a051503040c171e060112080c1525080115030510150203 63
    0x80031580e4510102546070702c80d9084036000b05000700003041c041760001003c2e0500600d41c1420b04140c01c02d80402417242d42195800d0400c210002c00180220700307050150f5402030000762029410301c3c0031100090602d15001e02d00c08400c0200300c2c00564220245e0b003140b1011030002d84c03c0b03540c9526025004001d0002406010044441c3d20303000130b03045100b03204840004038011455408a1281410400580100701c6c00f40d076a030140900800c007554040c41030084a01c128402414464907140d641000d49210b43e1410b803040040c0c440800040d2109840c2c1030800252207600c50707030b03070343d803441c141c48180c0060b0003007001c039a0301001000008000295000020904843c0c15264101903c0180d07601c0d4000d0040844002440d60b40307100048040e406029482c84000649010450041600049034400c1b1204003581d100700014040070710200d0846000304466207031100803503041050844401c00c24082400815a480000a050a000000a03c05800142509400c00c03c90b128025602e0f004840d0a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 653926978 1250 653925728 653925737
    0xc02120918090d0f020a02092a030705180d0203060403120f1b0e0f030d12110f041d04020a05010c3318020901030303020a090e0c0a120b150f09061603 66
    0x4c034000c650002520725241507005101e450b01d5030755036041d80392003507400c00001000d48491001c2d000b9511844081c5118100c507584003a00c841c1c2c10611650341031211024140120500b88401d00540c07404190300394010b03050b050a9020800d042c00c000010081c03031a202d00d0482c680202503600c404c01d101030b016001e246680304184920391000f00320380801c072400382c65030543c40b00382d5400d0100d00941050642c06085040060000c0d0401c680b0388035648150200158107900003028480a90118420215130344507040201c0301c4e182c160b020402e41000b9010366030500481c60114010414410183c204071062601c404503041c4155a2070345a0a0140ca54401d005043c08911403040e03907032110822810f90000c2c41d52205910b542c41c01e40c02580040c440000700b01c844131021400c41c003500c039041e0207003009000742507a40700c0c40c40c401490322103885441c042081c1042c8240210755070300079804207414800a0f105685401160180c0c17524411150216008000032501c0c000c1a82e1160008032240e000b40c44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 653928228 1250 653926978 653926997
    0x5030a0c1803060f1103011214030f0a180801020d0603030e0d0b06040f021303080405031b03030304110415030b0f09030c03030c030a0621060608010c02120918090d 72
    0x401d8800354010400141c9001c010300d0100007098064000007541c030070507800000c0c0581c07422024481a8000d81040a1014040baa20700402c202d09940d0485002610051070800011740400c00c443d102c1d6140030020008540c00d803525a9240b01241d900030860740c0c00865903003104c0d04c0040081c00542c4030a0b00032036140914241e090604411403c032503540000742d052195980c4041200074400704c0a41c14125a082c401c0c1034100081141200195000d80b400d55204c40c03400b020985002101019080520310441142030180c41c0002626005603001c010003801d000d4440101e0014a07006030040e4884001030b000005004403084110700400c450400c6420a558034082d01c2d64078400e14040540b00d90080000440f500c0c00319002c0c6401912542c4086081c0399203240104003685003407020880d41407606821410400c45200d040f00800c4914028400c0d0000c000d80a0344035042045039a000000000f00326115944145000e2901d401c001c0c1c4c4110542040b10506940e120000039410200c0d00c02c12 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 653929478 1250 653928228 653928251
    0x80c040501210303051f030b0114040213060c1a13140604020604060513090501030b06030d0e0a0501030f0b03010e160e0402060405060f19081b0c030f03071b0305030a 73
    0x249407004090000e410ba010360681a60b00f2002004001d100c0681000d45e070300710941d10100329030040c6c002c5010b600720552650401c00c0e42900e07400038803d0b4a00c1a44100003500c0c603072803a91030f540129030f40c9041078070b801811070602d039420b180003c004034040c0003520100038000c0780716400012068000d980c41140e1412001c1d0a030341d901d2051304c0c003a50002003408200000b0703200d20f009140c50f003400c000c000395141d075486c41c0f60144c680a0700f0440e0030182d01030801c4030509042103003200b260036928003521510000004900301030300ca4003c060405403250200101130109400c0070550b02d2001c4d000b080000c1e0350382001525035071003580104003003100c00000a00241102049401542c000f1700061406113014200011980260701d12502e6001c1400405075502c4540c11180c0030222945a0507090710300807088082c02050070001c0340c1c0d030340000d2080e0103500030004103407164080c0080c507940d640c0e00d501400303581814260340b090700110000c844103020958000013860244038600024051005d080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 653930728 1250 653929478 653929499
    0x30b1518010b091503010602030403060e030307120f0b030f06040218070806040c0306080a06050a2f281101051b190e06071a010909050a03080705040f080c040501 71
    0x4522440480480d80148640040000109000714000f8000b40c0160003040e0b00c1466074009900140240e000842c041041c4807007805a1107805480303034040c0d8954030307050070302074142c2103030002d6036203000c1d5681000e803240c58240e0700480d0b47c1c40c40107089488201141d50030660f160000c4500701d006407040181d884810070a008454090300d015150f507401507a0300c00074403005003010903c03402059110351002800c01c105120b9800c107107000b4540411145056000141561022a0014003400204801c61400c0300c040c0000c82c03200c100340d241c107581c910b039100d04400542450790010175080301c07000c07001e004641c101030340803022807a21000307001595509182410300119002070452200c410000a41c6064168100910707000b22400c10f07010703248404c4003140701e07504504400c0310f11240e2690303d682070554104040340100105003051060001c0344c1c0e0750584540303a00b0402030902c03000d8004100321500030410b84003c1c000c208500e4001e00d0744d6035101070340e0740b0f994406503005038030740070010507000c041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 653931978 1250 653930728 653930749
    0xf0c050408060106080c0409050f061206070905040b06361005030f100f0909050f06150607060b03031204061a061b1906230f040f030e0a030b15 63
    0x81202814450307103022001e95401c0002460121480c0c0200030216029082d407149c5c41c01010780e92400440d9184c0b200a100c0500d07001d4400115503440042007148441c0c0c0304c10303408152001510041280c42490300071498902810442801142c50000385049104441c500900c602c1c0b900c40421072100920801d10034003442c610f044000041d810000182446800c0503030301c6c0c100002c0300500036203954842030204410740070b4000c2d0f03070256240d000780b805129040140c0313050308420300302601d40c5e4208412408410343e0807440150080310003007401c1082c0880780d44480e0301680040c0a5955600c400c00141810540071a411101c191034107601c0c0100913041b040400c030038400640340302c1c45c0c030040480d00020b0034000506500a4429840c0d8a460704e001e180e100d1841520800340032505480c0f80c001540e00349400c08944a0080c89001041034001c03d140d20a500a50032001200b40e1000d0750408a4031113004040c0c1940050344c0e420004100b1851041442c4511610014000411a101d0810403d00e00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 653933228 1250 653931978 653931989
    0x2070506040b071b0302100c0215070c030507082209021204030305130f2001140f070213140403020106080312010e090a02030703050c091005010c0b0402220f0c0504 72
    0x89000180003074038801046420030f20a040640c10802210404e0070402c40c4400b0880042e080f9440c011134040590066811250b202e0000e81080b140c1c020502d948035100404120410804109003014540500704807812160090103440c2e5407030051002c2c0c01c80310000c5d40b007104d04103027408001504072043e10a891085030100c4001078a0740b0796441c101e01030301010b41600003808504404d000059030722110901c0081c0309899003080d004420300d0070805c02d00d20b10002c1341031111030580c580146003414100d644820861208544909560010036410346540c880c88020b01c0c40c0440301620b07102030103051449180729034001d101c007036101c2c40b0b0603403280919240700f1121811071006020191080d20034a90110702401151209841500004e24205107644251116007091864004038180344140f544e004c0403121205014501e0100020300071561180d029180c9189003012500315640c107000c0e040243c40850305400da007004680e02800400903000c400c00882d14146c1480956070081040c0c0b01200c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 653934478 1250 653933228 653933233
    0x3052b14030f060f06040303030b10021f02030406020417030d0c181211060a050c01140106050d0513020a0906060905150a050c160906080609010608071a040e0703050f0a020705 77
    0x11111074030b1009a44001c0c1c4215845100c148000745991214409040107502950b030100c0c00e040d6a40600040000b60412401150400c0b03490440c10703140c012046015044114005980356102c2c140300d4000c0c000c1da000015006403451501d540024000007820558014407000c00079402c8406040d0b80c024a1800a2a040802c01e44204481c1040c1d03200c061101703000322500700c403099903003002481c5c90340b0011043e004200042078524124100740305000c03100e02da0041c1c443c442c0d4140301000d8058022400c00b0170150b030f101d200090007218106201081305038080c1503507101d00e132900703507001c00340030a40241e400203032600e04002020301c0c12410150243c842a2292803400c0ca81ea04100c600740d0004148507440e204001c00e05110200d100d0f0746500822206400042c41030030302c2503035820100f0244c40140d5580c10301c1020701141c01d000c2082070403103032440000e003281041028004400c0c01240d003c070070b804031100100a074031901508a01e00c5014a4810b01039950340d0000440c08a00500f03a0250095 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 653935728 1250 653934478 653934481
    0x301031505071d01110a080c0601060c0302030720030f0303070f080606070f0221010c0906020a0309061b0c090c1e0504090c1e0309050d030e06060603060a03052b1403 73
    0xf180c000340c1ca01000c0030185484105c40703800320346451a185240208441260300020160503090b414403030a405807044c0d2030f040c001d666040c0c4000b9682d0042d04c00c05004c401216259142e8604182845079201c48040c3c00d0340d50b005030140d070583c0c0b80e81003250403001003140c0310303200c0e081144112411440341d0401015141040090348560b4001c07203560404036000039030528104417807880950f80182442c5002c0000c19040c0300520000e01302d80903136024070155030041910f680007a402684507802e6543c1440c11f8401100108100c03c400840d91101411002503844e011038242c01c04d4128580d202210340700ca2034000d1180c61074451500c00c40c0e44441c0028020f1009105100d544e4000d581982c07028603125480c00c41120413022812000150000420383e140060b10800200b8490000340d031803103040810011010900c0309484081c0205454032038000000090081d581d003100c43c1c1e020310f4000f400c0b1090907480c003015a80d906201040c580d240c0240d202c00d069410721400300c2d200003076000604941907 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 653936978 1250 653935728 653935757
    0x9080304090e03040e1501033206040612030903020f0603010b1e0f0c0f0607050f0403020f04180b010e16090b0d060803030c0703080f040c0314150408030103150507 72
    0x900b01044401c0441c081000005064074654040d640643c150102002c40558100300240483d00000282c0c1c0b0380d00c0b00031000a4880490f001c184001100d44017200045517240000200188241d40054964807220303400390060540c40b01746903003178030b02c00c2d80ea40c0c1030090f1380b104111290100740f00f810764403c02000070404a8000300482e030490039503507110380c1c100684400c5103156600004124100c2c2d80c803c06030b00005c01000c120701c0d43c120006090141c40e000022580304028412408068001c040c0c242e42c6031810340b01c6034000a05144550007110340c0801510300111038900030302c2201c14229040380400d5044804401400200c1c001e03441c0e200d90140ba29980100a4006035942c00c50350b580c4400004061009000540c4a00c8c09501195507940e150300c2c01804904002c0e00180e2115004420400082d10b250180d5041e65000200c1341c003000e2040f420280b0b480400c4d284050081c8105040c04200200708015605030b9100c1d07411080402d03501000e00c2d045840481c1c0840004911a402060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 653938228 1250 653936978 653936981
    0x130c050a030b0402010c0c0509010b030a200f21130309090c0e090606130b0406030608010e03030f130503040b0d0b09090c01080709090e0a021c11040b0d0506090f0c010908030409 78
    0x1b40301d2003a1444030f807a0359504000f03144118264080c0030040f90000c10403c03a429284244945005c0181c50b030100d03486003140c074000c240100e84a80c01c608100044040c000700110190b101c41422854903004135103020440440b4400c4001c4007100407c41100010400403a0342c00340e041d200d500d654600b0444001c0c10b0070000c0c20f0b0300140469820003410000d5403501042605400c0191402d2503d00c2d559900d020401011200c165001c1110303645000610006074034040304481e04002c01c41101e00203500d9100d68555145140d010087c51444009000030741b0704010000b0301001c201c140c0b400c0051100c950309202880400300c401d60070310707086070a580c0019030050300344079000001450007904d1940c40d2000c40017107031554180d49030b079035102071001811072810142c0e408082122004400105449941d5400443c2c0b80b0400103204c0c0d0b4940740040d1941d1200c5040454441e000030885410342441c816090300c40c10034285041d51406160007010055000740829003ca603981d1004529003407070500c4020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 653939478 1250 653938228 653938247
    0x40b0a090204020702040c03091b0e0a24030c0e061f0815040c0c1707120809101418010c0509010e060d0e030a08010801150315090803130c050a030b040201 68
    0x2d90141c0e0034401c0a0158950744100700424810f900c000508211506003040c400880468044000394140d6040c00166805e52405400000c07071900410340507061107083d0910000d081c40f54510100e1a8800014415208180c00031909408640f0f030054840710284140c100700d0340403e00050150350344041070b0310300c076101942c0d002ea00308041060b03040d107541c0080c05823105602d5406c001403101d030000051242d00305100c0141d410010b402483e00c0620740d1880c02d135182c40d0000c0303010b0103c40e030006100302c90240f166a6400f02420b03001c1266142c582180004043d0a07140e90f42e0000640701500c075800014443e5401d0b0344500e032103550402d0016001100c1c82107030480c406070408000c2c00f50007030188140c05070400d40900c00000d5911a03903015401041820140d2002c07500342c1c140041e81c4a201c05500b10741c003da0743c00c5810381141484406110000e0300340914000c10301e0074004200918031401541c1900110b00c036070441c1d5a416680c204000081d0b0301400042c10058801000c18010b45c02a2241c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 653940728 1250 653939478 653939483
    0x5010c030509040902060c030d11091c03020f01022109071a0d09080c0708060f16050d091208010501020f012319091b080a2a050a0f03050705010206040b0a09 69
    0x100d0742c1500d640c0070540d47e801c4499480303180d03400811143d05601e01b501034004007010394907090b4208043d8400080600c2c14036032010075603900f210f00d0b0340d041c144288000e03500300e503a03c0d00940d590041c143e01c00c0482221224402c815003080000304152034800b080e4403044074110032054042000031080783c00654043c082c0f50344600d588601c0d000020f02201d0148c1004142c03800500011442c00b420242041c0000300f240b0400f4000350708200e002da4090b5900441d0404a18005171580c045030302c1000100020f0b03501500300032100e84004041c66101800364180e48080e0b0075155803140e920105803d03103108802020014013154080c0c00c071406500c9485d80e000d0090030040014075550f444610854100070004e0301c40a03107224140c1144602051020000c140744401840b1441c050780301c1c040c07410070a0442280d82c032001084201c1107004040340002920008040040711030382c1c2d4480c40f42258052101b21102d0003a003c00080940c004900c0360312031900f01c170080c240c9546201030300000b440d015004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 653941978 1250 653940728 653940731
    0x126070e0601051e03100f0b0328050f010807061416020301090803011d0c0708180609032d01050106090b0d0609061805010f05030a140f06130611030105010c03050904 73
    0xc0d4140151307040c003500c210080345950b540e82c0c10201c00540c03840b03002e0307089004580c030b41d01c00811085907182d0883e03500540e4251940f00c1c00c510100791031486c074808101030010380d0a00d070034003c100040e0101913048512910455448a81d50b80c030558298401c1c2010988612040c006115003050412070004140d100800019154810355030303001480c0c0003a0070401900c14800321075041e860f901c4d8105038001503034540300c1e4280304171a40c03040c070b440c854590103008011802c00035104070f4540c0b00c1514110b81d002020f4504403110700c60b542c2e000c941c180348082007140c9240440c140c1d008042c450395060b00d285985100c40d0f80c1c01c000c80c400e403692007010301c540d08541d100300000380040c047c450710025090103205d564401c4210454982078410603000400380c040011010042a640041d1a41314940d010004855010020340d006083c20144440002d0318090b5400b001000c61040b42d1081030340d4801c004c1003241400030220b47e5154042406a14081340070001c00c0d00100c0d00442c040c02001000520 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 653943228 1250 653941978 653941987
    0x71b0504060b04060306082e090c0b090f06033106060f06121e09141014070309050723040608031b0a02181003080f030126070e060105 59
    0x114040703a8941d8071a2050380004501840503540c54020040205003e000a100a1042816001e441d045c084e605c1284610320a031165410303a41c64011142e9187c1040440e030308643d03a89000200b176072204d05e100b40b052100b41c50401c06440d00800790307400749543c00040b003040c5c6024107c1c1c94505039010400311011070300d9000c440009055020b0440038002183d08105500e1801d2030103806200403040300c0390814140075001c4100074204420103c24580f50304017140d40291801d184003004842c40030051140903d100854429002e500100074800f20301820300410303030f9810b50840444001000040043c0c11408080005904800344204100341e0b01e0618144900d030311000070704646459022078072a810100d81e00e59518a0100c4440c01e085051000d0503482d4a40d0380001e020301d0750711800300c22008007034021819221020311290050356004805a5582031000c0e61484250402d00c43d00c082c540354102c217004002800c41c14051401524001003032182d00308803e10b45081001086181044014403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 653944478 1250 653943228 653943239
    0x1305030f044518080c1501081603030332011a040506040306021303080307030b0312091c020102190309090608061306090303020f07080901030e0111071b 67
    0x10001d2000709120118002a221102020709005078a20000030300b4031180d40341401c1d05035510000081002c6079250010319861050989042d501164401500300400415111000c4100080c8004804819403004507241e17a516941940c403e141d101c4500000c90009080001a0203a000f5195032001c4003452900902c0010181003031807142c10072004103402d520010000c81d8003410280420b244000705151501c0d08200115255201e1440014411a40050805071840d4002d82040107958055116a5030b0f003000b2034010043e0480c111014881e0081c2800c840d00121060100c0351148005410400800243d86000403d0701405030281c0c190b01980c2c003034a000d070981b0410700340083e12913111540b80b00d00740b241c402d0444062b600450f5950380064240a8030460381c84d148207a06030b1008020440c048146001c0340a402180322111800b035001c10701c4030420000c1000341c002039600380ea04001040d40308090724203035220741e102c0c0c030580041000f910021a40070b00c042c04440a940000042d140e83d5003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 653945728 1250 653944478 653944507
    0x50f0d080306040216030302280c030e1908030c01180309060e030c06030115120605010c20060a0507060c08010f090902010c0807060903020f0309010906050a23031e090303130503 78
    0x40d17011070000350300150b841e0040074040502d00c40b502e09188055019000b289015258150304180030f428030841842c440610303501d84e01c0740e504001d0280300c040701569981200940d00e8002d0f0070b100f003465082c600e50100303031034424859101c83e40c2c00da0703902d168040c503142c0181d88440c400d880650300340c01080c0e101e01203921010021802006050000d0890302ea1a20700101091107000c41c0c00341d01c03030800c102005660390100c058010150000c151455403014100c4c144500c5001c0030308140c1000300450200c20301c6400a0140c98454081c0000348034030300051008507110031090046c40130100c000602842656034691000c40568410706140e07000842030f454085180d01701c030604695858603055181d08160f4180400c1c080d40e000000210b0509556200107001e0603414024603040180200c0e0100f031691103070080e191003004600c0341d2002009609030f200c8076540211400c80116117902451444800041c0e4041d218101042c0510305586410000d007010f0a80858143c1d4280b20501241d001104c11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 653946978 1250 653945728 653945767
    0x90b09031c080604110702060a03020c030c0a08030609090d09030303020c010b0306010906090608391207030b07020d090b130f08011407030207110405040203120a18050f0d0803060402 80
    0x1c1e10340004030f252420420080d284600d030a0303103548030180090001a100c1070150303180d50b5001d007405070701ea14600c01d000349140182d48109140d80716004145060040382e8000b580201c200344d46508a1303aa4105049540b45080d500720000070b284424204080307131003540640f40170060480042005030f50000001d2070440280c021a410560b900e00420100403107100e418000d141190140a50540b50724a0100c0c40003058104070020301441c850440540f00302d000341712010001048943c003000c0e20b484443d40d07001540000c5869205800220b40158000116504101510740e94048000d082030350100789500200004503004980e40f0002c15400c2203845e070b400c060071004000248030106020481c0700ac52002d41300500340b510410000001c14403036850300d00c102c0001d031030109860312544046440c0c0750306c0d0385408c60b5400012130480309040e40a410001070040785d224000b01c140d224400c01c1140120741c80070a5000180605200005160a010f0359000000410060901d03504210342c074581440e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 653948228 1250 653946978 653947033
    0x507051905030409141e0106140706020d02030a0504030807090812180a060203070618110f0123042903040308150a120201171920040909031e090b0903 66
    0x40c0e03030300700b000e03008465207403040c404031b0222500d10310f524092025100040244148550200c0091444e09201103601110049824108115a01d00c2c1101458000301015941100004c600801103980b4511981080080d102c01c1405010104070034002c2c624103620003040c1100507423215130848a280c0d07a1034492001003550f83c0295a40707403038a207001c0003190410822203003034803000a19074000c00c41c0d80c00518040c840940350810751034a6100166940d4044680c0c1416a842c40c3c4500c0e00241c0c0303460003070001c0704c1501c1204128500c00c080c0010041c29404040710381900140000f4000c179203e514003d03008400010306110342400000490719040d5250803010240d1520300342402156800030100790301000302c40441c1135034104110045804c0c1e445241c038401c00b03500ca00705101100c0f440c00d5103055030401980803968a540c0c40140c0d03801381c41d05250940c0070071107084001440302ca498400082039609e80c6e4a640e40d003810944441c009070004010203070140301d03204a40c10440d0041280d003180d08c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 653949478 1250 653948228 653948261
    0x8060f0f040603211409010f020a0507170d090b121f0303090f061b0803090c1801092306010c0c09050702010b04050703090201020601090902060c1903020d0507051905030409 76
    0xd260810308100c0207401c1d031000c100811002c8044c0b051400345d06032020180246050348400c02c10105c12403610031510400340030350140c400001498948849c40520005000082e25450000400d0580340c413030703640c840d8410f040303400c00500e00708135500c2d00040da018402501d00756055840882c0c0c84203245c0b01c0d400440101c2c411050501c03d20498482c41c800504d02441c0c0066088203196480e2049034902d88003e00c3c2c1d03800131010070300d904010704c60381980354405441e02e1102000983c05112a29080c8503001d1502e161030380540c0740c01c0c0c20904030101200585030761101502c45000440725210780b08070540c2c0450040c00023003150034050169030300403296580080b8908220004000403204098451410305103088407100050760042079041c11507031101c00000b0002d61500204569101d1380e519443c5c603000c0c0f410141c041100806054901c05d00079404c030f400786030881c00140e455219060003c0c00540c1720341c05440191040182209145120b07005682c1440d40c5d4442050a880801d00840c00c0d80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 653950728 1250 653949478 653949503
    0x403030c0308061509010c380a0506221d010c11070815130503130f050409350a110c0d030e310209011e08060f0f040603 53
    0x55400018030703822943c220794001c4142c0c003803c00781140d803007107000040c14001c80508080c28005031000040381d1905459101c041c111040e02c411030605c2e104607440803401c1d00400480d09500140c03003941d10844001e0000300c0d40140012064410611002c0c2449015440d50303408880d043d10030032841c007180860701c004100c42c3e4034064060a480285000e4002d01d44c0254002c01c101c00000401301828850f8824001d10343e150411318003106140c030b2002a00d00d100000e200c108403645580400125000c0e1120110020344880801c030036074000d1070001d4420121905142250b0140809507401469080405581c10050205441c000d80200d1052008181100c0510940940038010302c004000b08a40482c00d04030b940d0340c00b92030740b43c6901c0901d00075021100e150444119a9083c0088000c842c00c042e00e880640e461004040c2d4403000340c072800a007030300401050f12004038801c2d4640039000c1e08d81252076910030003030000a0240104441e841603c010040c68a5102c51041e0406940640000844d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 653951978 1250 653950728 653950733
    0x905030d0c050d35070801090507050a1413150909020f040311060c100246090b030c030702010b01090e010e0403110105150406050609280b0403030c 65
    0x81441545484091020702441c40d000910301068580403424030742040746012031611020541d5400d02400244041c01011011405050300d40e00b0300d120714110342e0740440307a82e20303800740405940c410742d03050010500500540c04810702a4541c543c0b425032031900c65040c051b009104504090355940990b40c0c03a00f40100d400c4000703034070100c0c00001c0c04038013a05514240a030381816081d0f1143e0f00c00905016013400204096a0340d6104664140780321a08403050424201c0840c402903015a04110110316101a0b0f51720740040e00b000e00000400b903c0180080000c0c240d0111080b861420070901009030303915010800307403480300186000e4080441103540fa40345c041b40213802c40b00da84503400c0c107102c0300010401c892651554140d0654814407506032140e104c0e85000e071540d0b000d100121203d9402d00e02000090b80e501500403140303100c1242c0601c1032942d500103100c080e2248150080d08014000c40942c202e00328489480002240040c6d42e0400c540d44011003242c540098108400040c00c03079203c1c2c0c05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 653953228 1250 653951978 653951983
    0x203072d0f0e0a1a0f0a020304080705010c02090703240e150a05100c05120304032f1009021c032001060f12020f1e01140309060105150c0d090503 64
    0x40d06070302070030281c490402210015001410510801110b140402201c4841154800544d030990350400c1c14aa1039880c0c404000c0d450f034200c1d0148940e82c0c801c9880000d07066100703903203422000d600a410131a640d101c0520840203000c00c01c11400190900c203001103c2e1080900005005004c884541d030814203200c0f42da000c907a540c1d5140c0d81e00c00c0300250350074071240d40c441030030750382c088281d0601e0300f603115452800d1400c0c05411500ba1a403464040100030a0682000c183d41301c407010fa00c0b6407202d515403258034041220724201010850380c4039020291500e42158892000b0b140010b01420800300210101c0c0045041d1400840c00209010900d40d0010000741c008040d13140981d0003841b20fa400c00d210640740c00260702c81c0301d40c030080c0310030100c042d900c0b8030b0f440d01410080605208a00ba00505840b00803a0982c40e0050000e0b000c07480340c107807041e07021050324000c4000070f014209603460002044481560b0745540c030351074601002200c1e04298200400c1c080ca9410b40c440014540c13030042010b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 653954478 1250 653953228 653953247
    0x3040b0d05060405070246020103050f1005040c05070206210c0f07151b0e19030b04020f0316181103040f02130b060705010209030f0d0509040203072d 66
    0x10300070f500704800d20000340c1d0007150031540120702080250b054908400c00201d10000142807a00001d06030351802686a6085c6800c0c8465000380c80900080c0c656001c541401d40302100e200211030000700c000e214501d00b640080450040074641103042000c11b030002019503204c401c0150300c01038900c9404803240060030300c01e5448030005004a04007401c40d0032040a03449080c00c000c210824950784a84030010561041c0618108040d900c43c400d181c116000e003036540d0401502c0c4c0f01d42d44a070401d101d0180035448140907030b079104844400d44e0b2a00e5081c4060301ea0b10703000e01075150007961150240c00c24a603518100030207101904841601102c21160111a400150740352404404c00411010818000c0e810001079416a40390743e5101d98401c900740105000c2d020ba642c405000103542d01442415009031885420403819243d03c0440d41a1056a030304800303910802264040c0030003160362505038007a5a0003515800c060b00721800c014a0003022000d107215200c1c0b03800c203808444c8070300ea90010650 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 653955728 1250 653954478 653954491
    0x1e0e090307020301140f01090c090b0c0106051c051c0c0b04050706090905010b0909280203060901050a060207060e041b0c0303050f06012c04111b0628090503040b0d05 73
    0x2030032509210141d00e4020768140030323800400d51152201ca164502c125162002004800e06140d00c80300b102c00200d000e05524810b80c0d2041c0b402054041215420300e10124105500030001c01d5192040c205090202e0b4048604200b130003444990312022070f000c0500d45102d0351142d0b000d00380c06401c042c030103410001943c00002e01c00b0315200052203003100010485201003021501458541d030b4a030802d94141d00030a1924191504400d084154105150040c50280f0000c5640442e16a2507200b032082c500e45500c02c40d00103900c100c82c20080c803030049058000390707903010744007080d07000401d10a10701c81c03118031416000188400b4000030a140c3d140c82065046080400d42031018204400000c0c08407031035050081c946035074540b0f059810140015000150f0901a00a00c030f004841c00c141d0700c05410244e000c1e1019054030400c4d404a00b0041113583c1b00f13040e00b4201d82403107000d00d0406510010105080407031955103100da640481c500708054070080071403802503603903080c80c41d40c1035050380c6010303090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 653956834 1106 653955728 653955761
    0x4060b041a0c060105061e190f0309170a050d05090c100306030305030103060207020423060f090108060403080c04410a1e0e090307020301 61
    0x90022141c81810801c0d59004030382015119128801c1030906541159005121914160018100a456104412801042020b0074001c03a50264030030381051a946400306440a5014040c15149149032a0501507581c0590b00c0d418080807109040750f01078004140081c03503038862006e4a020341d00d900c40c14806820a40b841d9510340450f030748806d004040d90036140e015a03010707001c2c0d40d044039450b0340c5452641e0310350703101c013030003500301030402c0380e00c107807941565000900304000c240c4135061441850545801c04208022001c500e2031a000d019030008401041666404159980d01c80c0c2c0504065100e941d8800c1d01e40010f100f10b41080108800d0408000500e9140050301d0340c900b0149a0b00410120b403c0748004100496000d683c1e074401503030130080c0482644452680d13282000b00f244154025215100000c1441007242d0066590307002148841c2941b50902918061100b0b9050 = true := by decide +kernel

theorem cover : BRFrame.Cov 653776978 653956834 := by
  have h0 := BRFrame.cov_init 653776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 653776978 ≤ n) (h2 : n < 653956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
