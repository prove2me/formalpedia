-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1937
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:13:24.009632+00:00
-- url     : https://prove2.me/submissions/f4ad1b92-b3a1-4e7e-9b4f-4d927c21941d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 348201438 ≤ n < 348381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 348202688 1250 348201438 348201443
    0x90308070f03020c2e0c0c15110d09061110140a0605030309100f09211403161101030f11090406051002030f21070e090106030b0109030204050919060207 67
    0x41c4c95540c4074100340a0741460108542d0900541e5242500006440c405500320a00c140e203005030324007205d0f588111807140e03140c00819001881701300036200d0b250004129040d03d0380460013050169040c01e4001e0400071140030b40b10070440f040f100d40700d0b040410030030801c0c802003420081c0903016902c1c40b4070924600032948040301e5400c0800004580c1000b104617a600706d00506091818140214240c4610001040c000200b0141c00c80014040f04490201d4882c500e1800d000007003c0c00b1030500c0b264000c000315003110240c200700030004c3e4400a03081d0001c055a4000c0080c60b0095226006800400e0700f42d07407643c1c0490408071120344c0003105000400c010101100c04000450301e480902c80250000b43d5100056441001541403920080c805031100e01503803202200901002c02903030301c012400b03541d14008501030b00d840d40841d26180c0c102e0742c00740403a803804000440c6001d0000384000610b2001a0289a80c1d070301045002d941809440c601c91154040c00030a0003c0b071400c03400030341c41030310117 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 348203938 1250 348202688 348202693
    0x1906091e0b090d0f2304170102070b06010815041a0307061707050307080c090a1701020a140310050f0f09011701150b0403060b0103061a09030c06040e0c0307090308070f0302 76
    0x2c090614000d11204c0b114001950365440c11900c1102460112030b250b44940c1c00d641801d20000074404401d0080510700d642c0400090b80311070032850106e03c00100070b803030749040c48041c0703003000107840350800e501036160030444004c80e4507403a039440340143c141543c0003070703801d40140c50001c2851074010501c1d1a01c00c01d030b40284030041c0c0e1421000c50702404265545000124000046403000b40c0d4100a030661040c01422003200356035822051042e41c40f0300320150150307500400d40c469015008140300100f2000500074a18500c0c3c50101d80807031981a001c0d540c4184050082c1d070401c0c1e1a402d088000542c1c0103000503007656100c3d8120800c0b0001d81c1690041903080512a18810040b074011508403150b0301d044604040c11583e40d8005800602c02032810981c3e600030018a4250401c0c8030609500c010310916912202d1030107050400140c104654016181080304014640c031102d841c03941701034210071064590f00e4900c3d089402403002c1c0d02c081c000f0381000c104481803015180c011540503100e40c08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 348205188 1250 348203938 348203953
    0x605011b02010e0a080d0e0f0d20030307061406010905060f0d150f050306090706020d080c120f10080111160507030f1b08060411060a12050a060602010e1906091e0b09 73
    0x3c025238501c40001c2c290b04102c1646440d00007420345114500d80d40d030000c40080c0b8a80303542001c2491500595410b4981c02d803140c4602d00d144030384080c8550010f00a291880b1500d05100c00b04110784103000d50100b2100e000500c01d503c0c006554015a0004210a12030650680d07a003009000d8104c103004844c428000e010104038030f0840054402c0c1210301907000380c4000c44400030141c9080000070414003408a080104041920006040a10030030224000416606055500a001581c690410301003071380340c010140028188030701910b40841c403c0030000310b21251303480d1450030714841d80d00081c04107a034802c80d00d0400030042c20101101c0b205e80b4028558650ba011403603502c0c5020f4a01421104992032410814180003004081281e0300c3e0070700703001140700d14012401f2208100c0300301c4840f070ba48500c10300c0740030750a021b915074030081740005103c030032103c00e204502c07d14110f800030800f42d900c0e03c80c18100b003625005a84010001401c2d640c04150f00c0c00c0c6640f80d11401c49071060f96004440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 348206438 1250 348205188 348205217
    0xb010b0f04030609211707030c05070501050f010303020f01020c1e03040503030403050706030b061c0f0b0307060503092122090212160503010b0906090411131401030605011b02010e0a080d 82
    0x40c0450781c0f81b912040da03005140c41d40c2105800a1044a0098003085070800038000440ca09028a60051000c0031480c9115891400c0003428078901a041060590041000744080340b40010030301d03a00c00045090100d501514a581441e503c01c580c86203400d4040810300000340180407034080101d070496142030141d000450100310081c40b030082802c844000c0069031103480c25280e480300160601d01100000c100e8001c40000f450010981d001d10001980001004410142404820036014031051710402031054038588240038016991191100003046004050030741c0c00480e000d005140e10b0304110343e240d401c11030290508004444c1c040306500303402d0a0011640c4074404030707412a412010414203151000d000c1112903440b845000da8020345490b00302504e000888000c1003601101100c01e0f0070640307040741544c03180d003045400a0605180942c06c001303507600410303010380001000c04003c0b5401c00034401a0340350ba006450b0700b40c00059010340820003400010303070003411001c9610341d02520008003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 348207688 1250 348206438 348206447
    0x100914061e0c0c0d15150b030a06030615030b1914070c120801080d140f030f0402031506010c0b04050114090c013e0a050d050304030e030a0b010b0f0403060921 70
    0x1004c010a014000201d01c61400313030a601082403065105050340c4607a50703030100c0f20842c0c0c0044d02c5c40d102d007507581e44041007006114803804002004405100307260500c1c544510b034104800801c0040f44006084040d03903004102c2d844140140c140d02580003507420640700003041c0466401d000c07191003580420454a250145100f581214203a800410501c4001c04040340c801e42501c2940810b840148554035002c006000514812206550780d24603500d0b040c01014600078200751801030002d4500c0030300000b40d031300088950441d0f4000c01d61200c29203552420a004002d0044c0301842c0607441810b204050f6000b1411401410090b41e42c50080c03400c01c12050b0140410b149052802005502402007251100b0030380a1201165002d59240c0c1041d030310344600f0044c9916a4900055002040004060308004281000d200641c000e0454021076610840e54040600079603550100108401c1702010340303401102c021311b500000a000d026010f241094810005900c0740c0d0f403019007504a1300c11144038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 348208938 1250 348207688 348207709
    0xf0a0e010908160b0f0f070609020a121a06060903060709050a08010b220b090406020c01110405130f150602030408060f04020112020304030e04060308120105100914061e0c0c 76
    0x980c004103000fa071034143c40340482c0c3d10035444000340c0c2c00c090121021050012000d000d040c3c1c014040842c004401c0d2040003407132255504a03000c90080300070420089401c121400b0103281444600c110705440d8140010007138040ea612460745480740c8030400074202d500144c4641282d00c141e42c1001100d80716810103090314001d06055811014401040483e0300706041d0915a001d95001c0018045226401148103031000329025628a600010000f0750764809101c0d0f075034107403000381d942800e282c00c000008103202d58141015481035110760902d8804a1998010040c500c025003225440036983c2c040a501d070307002845029000d00071540040c4409102071108e51086505039903200150008881c128004c6d0400b90081d0100103500643c16500d4882d03204400c0030314010303440e158039109422800324040c14140c00c403a01074035104e01c1d0800000d4201d80c41d0025180d5003540403032114031800c0850070902901c031804030340448420342007146540540003403a490044100740c2c2d000c40721880070310070728403070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 348210188 1250 348208938 348208963
    0xf0e0604060519230906040e0c030907080d0516140d0f0806030a0816030302120c0d0f06050913060221040b13030210110c0a060e070f0509011a0f0a0e010908 69
    0x8581030005050813484000341606003004021074105078441e081d441c44800c04480583c0b20060000900c03c2038201041408014491074006100c03540c0e550344001d0507402107400710741100c240c1c841c80f4403c002050100b00b0305925507000b1210040c0442d00000d0440052480400204030740ca03010030f40608000c5850401190480d03449882d100349800d146251145d601c0d0140d007010390a02941140480d41d042e41401200c00910480d05d43c49204000b5045610721000d48050500d040d0b420041da07240c600300541d003c0d0014204042c014011b0030b20310040d10850341d140304901a580d4200c803451481c400551701031030007134440c50040d590b905200c15000300703c00d00180142c1c2c0000d8806078040075903000030840780c4c49081c00314200304030703a044546002824102210002d403038006448201e407081003020020903d008000541600d48408500800e2041c0602005200150145001001c1e00c4c0111010f80314290440c07a524551080020b080315101d501144c0060424840011a0341c40020441000d01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 348211438 1250 348210188 348210227
    0x20090c03040201260c030a1a012705040501030602130501050406080a0c110307120f0309110402030402060f0304110418050322080d0207050a0605070b070f0e0604060519 74
    0x200c4a0300192180d13940c40454a11031841201c6011130108119045801800003001464490400865520990780a4510000d42c003281094080309031380d01041c6a10b10612686d6000f81c0f010240d4080311300c00c04250049600f05060800001c01c112890380146030411502c140000525220401100d551159100b8000014420030118500025561000502c100b10341031504006000c0320849055400002064450085400ac0049665080580c0401502961a0410480b02e241d940d041d440038080d1121070280764080300045c00c6446d194100c1d20b40d030b01c2900025483e0314103460004018482024001d0155090490541d8a01c82e1200038150b01548040914100910300c40d554500000b129829074400c1c5a00000003080d13079080c40035141080aa0f8041d2074940d081100303001600e11564444020050100510400305074007a2499812200600c2d148900384900007007200d550184655103548810000f0700000d056400c6402080c8a198180c030002c800310080e4416291903005071070030001d09 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 348212688 1250 348211438 348211441
    0xc080624040902090411012019080c03030115030f05060906060904110a0f09080a02010c1506150905010f0c0c05060a18031406011a09120f0a20090c03 66
    0x1059900300840030006000000d04042d690006000c95030181c50988014244414003201d0707507882100c00300492014950118110b28096400c2c2d82c1d40c110007248202c6c80c002c14622700c2040301801c1210346401580f02240d0b00c0356141d40602e2403242d507941407440442d00d0074458041307201c49402160302c5244014100005e0360303610003d01000c0d52141080076031059032911a140890340040c003074055030603d69980da076100c0d030464000e0700e03403a1660052060391340007210040060307030b004109800ba1544801d1a0441000051ba003c1c003a0030075400c605004400f0400141c02503030b00103210401c941c02680e822005118500050301d8806e500380020344a940d2880062080e410701c000200301c0c02115141408100c000c03d064000010440d40007203449039015404040441c008026642c0036020a00b0300b014200c46403180c1048038400e0b0035103140510184000503440314000c0c4000c160200c00341043e140d950b6038070320b40040300e680b40400d154480d1000b00e280c0611800c003001003500c01e80c0000c1004c0d185 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 348213938 1250 348212688 348212731
    0x150115020604080c3a080c070f031403190606031a040e10060305030901080106020f0d1b060515040c02010216110a08070602030408150708060904060e0d0c0c0806 71
    0x3980d00020204460340304042d40340e1031a0b0041c1605c90b0007000e44c98030300b60380001c401301e035004d111405c0c494440401c21204207100520343c6240840d074810390701c2200c0ca41104802e16054680e4800605281e00e0030b14040704000340358004040c03a450308100c841e001c0000b103413114420f80854500f072807040e100804a15403607507142450381c060a52514003508030b50003106601100401d56420b0781040395103800100d100425940c00014550140107240064485c040051300b009503106564540e540400c2010b0b0010b40806501c0c1c01d032003904a820050901040c030303050b005c03500c1c07880e440c62040d8026443e007a00311104030b06c188241c0c0c40d0040014080054414680c81e00c5c126410381c6c1881c0340c2d101c2a041c20004010208122020051401e5006035468914080d05a420490b40244c02d80b0704004610401c180c4a0340141496842481202d26403a00e44413801c0001c000c000c94415080244500d41c1041e0700705800200a410b07080c031520300351268646400310240c54120944010000c54581c1c408ac078813 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 348215188 1250 348213938 348213953
    0xa0902090a150f181a03030a030b0a080102031b130306050c0711060310030314040f080706081b040b1e0d140a060323010b061309051003080316020c040608150115020604 74
    0x14100402d15a521071000300c5d00019040d43d0021003140c010941c0c48900c0d1301c0310f00300391411304010041c0000071800c42c135100a030a840c6041d02c04500c0c1c04601d0000d240b418000307040c0742010255410010411451803c2c0c0c1d1054400d5000d284207442c1c0c000441c0701c880e003030300d84141124403030144400759840e07540c95960260341d1080540c13030b031003000329040c000400c0300700134140814020413044004001d80d42ca01100a80700d8080508203001041c00b0f41c0d1030280005807402110200e54184840e56520102c0c4410140c05030000c4141c070142d5600052010b0186855411030702100c94081070400b0b1948803038010408031155440000d002600240440000711450f5108081040002e4000300c0d1204c11540081c4090f4820103414141c401c0b003d2041c4406001407154039405a1880e044040c12415921062201e000040c03d08180481c1025020100d9200340420441d2603406042400056200c0001c03d03103440f083e000c0f40185032852000019056202e4010341000c000f42d4014180d60380382ca40f103048 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 348216438 1250 348215188 348215201
    0x10c170f060f040e190c0e0106020f030f03090a0c26012703140c10060603020703080c0a030b030a0f0b06010f090b0a051215010f0f080109050a0902090a150f18 70
    0x751140501d6800011004100005c44412441079000b022003a041c424401e262201c1a08400210340c03112202140d060f1000007100d0451000c0c0c1201601c03941e40c40161480c0c0f000300f84005020f040702500000e114043e9040c0c1c24134000800078181030920300710005500725202d10303104007480110088065031146242c0384802d202070103450103107091098040072078000d51000b400d0804592001c140801010502d108480282a00c0e284c154544819910010918407000d0b001c50802103000450403011030280e0302c00c2d0523499018060307a640c400941440d01500210000560304440c0010010300f141d8403030210341c401c041581e12082082400e0190190355900301c074141e041804000c0100010041049054520030400c2d48020b1484c82c0d1802c00041080807000c0c2c80d9014007040e502034003040c0fa000005141910031031000000d850b0b450080f880c01030512440f001c1d4000b90140c040c0011204030b40c02c00000d400020030040325065a808072041d20424601c40c0002024a850240c00422a640c1021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 348217688 1250 348216438 348216461
    0xc010f140322110103050f0402060a0e0f0a0b0304060506040209031b04091406070908010c1422030b040b1302090f060a051504030b1b0306010c03030e010c170f060f04 73
    0x140d90020758070101c00d000300d85441055441da86030b000f03c090b00d9a454042e0b5a031104850300900305604059001c1000780c040c28541c0c07170500242c070a07004000d80b5a1064034070b2840c1c004042021183c1e581032220b819038030649050f00c01c40c1c00c0c40000f03001403c260088a43c0c17403070301600400800700c48011501900501c401016801600d40c4161004200c010f6840b0820003007981c00b40007582030030320000d40101c510740c0c0100c00c182d04107a841081c4580128140d0802d2022043e1150b030303440c0104a1001303801030042ca044c81030320205404428000c0c800a064403aa201e60f800340c0c9240c882c0c40818071004d1940a0095005203840005010b0720011000c054100b0000f4001d041101d455900140054105420826141f0f0303011808109015028a1950700002e4144c2544c011011915802e2914071000b401603042c4580e0346041c4042600c6035101600c136403403000081090342a0508014082c60003101e01180c1d0750945000704221320f602c4500640a250001e09040d100c07103245052001914003140c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 348218938 1250 348217688 348217711
    0x507141c051602060d0c0e0d08040501110f1b010f021209060703050c01090605150118140312030132030d11070b0c03090102061f05041515110c010f1403 67
    0xb4006840c1c0c14003410400d452003c0c0070803c02c680000040c038125405408500c1107a1340d460382d501050415085a0940c0c2c400c0c079041070650104a0305600d0003070491007100c42445a5422400d6903410262140c1606800340d071110102e1241d200100d0355140031140691040c0030800c02d0071138510300340c03000f801c103103119040041c1040210b40c00f444c02c485800c4021303030302c2030303106d5082002c510030411117149060005d0070301c0d41c1e100100b910a0010103101c0d00554600045003040040e582c2c1d0100801c89052105e6a01c0596a40c1c4400000c04200c0c02000c5002c5001c0d075402104050300046000400d018502400800315520400c40c200c500500b1024999002c4c0542e02e0049807035a0b00c00002c10741c40d02150015543c40b0000b9000918040740181040c248000c006900c1203407242903230640c02210801c0742c001c601c1e8001c00c844201d0b10301035a07101e81070000981c5418207601d90041091812032070000203440c10607030054015244207501004200c002028105400410403111001c2d540040d0050300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 348220188 1250 348218938 348218977
    0x605090f1909021807081003210c08030a090b0609160f090f0320030f1e1501060c02090702062e080106060504080c01020c06121b04060507141c05 64
    0x21458104e003004051514500c4101004441c9401c00e00113074110802c081c8070b0342840d281d601c50605540181c0084045925044400c8030400c0c8208155008581c2141c42d03680c0d00d0406040042c000d1490f004201c5090810b14001141d030b1a0900185201e160300b0b003c490710004104008031190501d540f070a50500c0503500012492010b50404000958030510b54010400594209100103281d4480307110302c01e5002ea07410310b5030000c020803c1d819054070001a01c0070000108035203420604030703003100718600c170305800000740c01d0340d20801405009000381c07020f43c00360301c50b0710301284c42d090708032503c07180c0084042c41d21003c0c9034041d460305480510000c01e60034468a91003800c1c2940d0080e401100000c0e00070505110000050005901040e000d00041480314160300200c0c24070b01440100000c00110b80e40001c2e4041c8075020341c2d14000007003581c0303240e07103c1d21b03900040d0140d08140819105211100d905009484000445500f070314041c1090071803160700c80c00111100d074060791004035003400081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 348221438 1250 348220188 348220193
    0x206310608070212030708130b010b120a02070206160c030f032601050a15140a08040212030309100f0f0903021e0105060906121606120b04050f06150705061303030605090f1909 77
    0xc1c6052b019040da0701002d9690401c2c07400a85407500007814a8448610401c481801a41c40c081103d403000d0b8414210300e0000d815080012007a0441d42c0050700200003103030007030101580f180b103403010381d070701158080c203c502e4040c0142e1901d00240152500071481c40800d0140031150403035610f41840c04e241281004490094481c551342110008002203000d210a01c002c6103000311003d003c2c006288011800c40c9080340b0341a07a19410000001c0c60039540b00d405c80710444440e0018041e881c8405414440084a0324009668002c1501d10000988030124541003074031040c000c450240300000d2050840303032206420003c2d42410b607030040c41c90f13100741c0304194403036032551110000502182e211f64141c626002c0f01c0a064890758510341e0302c1a031810b0100103000e61152042c5400c03130001d5a09100703076154103062400d00d100c0c0f518041d10f80d1041004006040c110f1100141001d88681c3e01401031542d030b4400c0c8a1000803c0c3d43c4034410b5040e65001805000c1d80b806100c550000000d408a075011098 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 348222688 1250 348221438 348221453
    0x723010f06030f030f05070507050d03030f020a0216080d1205060d1707021906120b03030c120405040b0a0501050d09170c010e0c011b020631060807021203070813 71
    0x1035004880f1410b0003940c090505810200c200501c07842400e005241c00c05640c0c9190f1a00254059144104590144801814486d603c03000041180800c11503a410104c04d000c1d540e0018040744c00074001d0320910206070308001188080024455840e03000014890421050240600400f4250842403201d6200c2c0803401680140c2c10000d241c580e4140eaa00c1580180a0320060b00f1260716000d048001e000c00540303030311000b09070b6440704440c00007035986581c2002904601c14107214100d00c1c07266080c04811352440030014001c682c0100c0f410001078414000b0301000140c20321845020500030300c5030032003480c40f80d046114080c3c4070729a025280c0c1d00c03004003422a9001440e075a140c5a40d11004141d0100c010492095810b0f800d0038000740308002200780c14a08111a40028007c44010070402c01c200504410141c01d40d030786450700b030340c07081d504610b0810802040c480c0f240050301e00c02c0400c180900204034850080e0500c03a49619650703d10100f41c82c040c0018000e0608a2500301d006008100c14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 348223938 1250 348222688 348222701
    0x1e070e0315040215131802130302010e0103061806080c03070b09130f09060906050915070f0e030a060c020d0e06070605040311150a060b0f0406030506031014010303090603020723010f 80
    0xc5e08000586542405220600d0b19805841146000e10402590342807170340081540d82182c1c0d0920b00310020502200c0101d026007002d0f403080305441107002a241c03880710f040c0c100e50251061481102c0c02c403042c40f020955180e05a1003065110b51040000306468241210054078410107420041600d480780103940c030403114450025124255503040400c20002140555078100b040ea4004004c040720003020402c10700e0740941040e00b88403d502804203140c1c00340e00303100c855100040545c1ea62135102d05200303014242220a000060254031400301d130301d0b03004155105e61042e000d000b05090901c6542c0b004000c3c01c005d0400e031b050100038041001000300800092000d210341d00080360b55400d20131400c0056680e5500410541b81e0180159144c84401409807421940300786800304498484202203820041c06038100c500d2903040c04025a401c1050030103060407a446651080b21250340c40004804070300030240020066420038281010110307404204299a10130000000356103640800342c14102e804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 348225188 1250 348223938 348223957
    0x1209042c0c130504030e060c01060e040f020a0b031303030b04020c0d1101050703060e06101e0c030e010509010c0f08090a09060801060522090503121e070e0315040215 73
    0x12020701d80e540e074100315020b040000c0b280201070100b0b00b00741c0e40c058092a8440c0c1d159000300c6020031200c28000007500420010680c000e07210f200341c10203003094500d44802c2403003a801401d0781640082d640340317044120792283c494954048030004190b0350441c0900b03000945d80d40d10940901c03804803042018001c44c000c0f844651120f500c5406e520700014251400203100500341850314100f04015001d919840f07070300600894030741e00302021180382900e0301400e0070820340000d1002c015010025800030380004299003e600d4038024880b00741c0044601d1b11030300500038002290041d4000026012082c403845840c0724017082400c1c90003000104030b1020540c2c0c022140c0303e8403450100982130b428821800508401d540301f611490582e1400000700142205030311500c1c1c1e540303101e03405000051047d10702580030080f070306000b400c0102e8141e0042d224184400b044440c0000801d44040c000c40c00c540348003030054060440103d0f18241c90130f85050052084c0c1c0c00c8500d00c00042c0c0d0600d0000000c1c4403045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 348226438 1250 348225188 348225193
    0x220f08040b09030f160302060702040e070b07050f0a150e211308010b060301030f030504050414010303020f3c0a350403020607023c031209042c 63
    0x2d161808042c5400b182400c0b002c0c10b0f41000d140183c145d00c45140581c1529016100ea59803400c0f503101040003000208000001d50140e840c0100c2c2c14208840207006890049086409140000114540780c82d0980c0c0000c2c4031a014400055403500303143c005041e0700b052007040d103080b001008681002d480c0542403450801200203590202c1e95452030070200900402030003006201c2c6244040340360340c80107000161030807000650758810984590215000380501810034000202040000030031400203010403005070049680d09510490002a1182c403842c400c0c1e091054400d40c00207100d0488a030500c22005000f8051403000549010061981614410788500c141c90a900c1d0405030060409a03854080b88255000941201403403810744095036011078009503900c41510024041012901c1501c7e41c4040b00b45441d4039000d620107050318025003554503d00d90312044401c06884500341036456282a01c140004001420242c1c00b10302c080d5100d5400016107050700c60704400012501000088a0707 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 348227688 1250 348226438 348226447
    0x40603050c130209030a060b1203040e0402130b1f0309080c060106030c02071401032c06060103271407080f010c031d0a0b040201090f0807050405060306220f08040b 72
    0x207080011030410a0a94020110300b00007038100041e890351b8261501070001900c2c2c54031004641d803040c07004440c01c050f5608880c0c1d0303103644411050b02090101d806912900b11895400500d038685e000d05c8108040003000a00c540c40105001c56840c086d000b2201304043da07504040b03002814507001002c000c80308070018000c5624040d401802d03202e80b079081000319002514200454110050440a0b0603002d08010401c2c140400c840540c4c0d00000400b10044a880015020924008108640561800e980c00d01070713110062506422180c11250701001e841c1c0720340c2c0c84d102041c0b90007500c00d01e60400e0801d5424240c2c2d00d111162602c1c0881503014860795442440b0004590548602100d801c5480852814105000c802c41d8441d0b0600c40041c01c0c03001802e0004085a1040d00000050200c0d215105401601e07660f40599440c014000d55020320720740004660540b60008945201d001c40740aa0010241d040070b03a9490018070a00455111091a4101000403000c0c0080c2004e40a0500c08507140d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 348228938 1250 348227688 348227713
    0x150204091d0708060703020d0f090807031707050d050402031905060f1e0c0309010b060c0102040812040b0a0c0f06050a0b0f150f0f090603130c0e011d040503070204060305 75
    0x212885000380030382c02844100201080460503da0011881c00c0060300d580100c0291000b030078680c1a113140341c0d403400301141e00300720481c00500300040c013030350b101d2b101c0414107070400c00200400c3d280000450030a004035109031450340c00107a482403008d016a50f90400d03040d00c451a10407440400c5595030810b4040007070b10380c06035201750340c0066924140c0b42c102c03180405600d50907401414150581d4030000000300040c00940040703406082c0544401e40c0d4554480d4258000c2d0040d008512060140300c84040e0240881825101a03902d10070307502d4541601400161035000380d030f0303208544454001c80d41030007140851190500c10f0403d0000810001002e00402080b031407200156842542a01c60485100c14038805503011056031402300c907a90ba030124000340d000c0c040c0410b0076601003070000030002c8030b0300c0038041140d8062013413502c9101d05840782c0c2c44510300c0a00b406400c01c00f0b40b030044c84802200e5031022680e0014020005d682c82e20310550003080039100e1725041a1240c1d801160391664 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 348230188 1250 348228938 348228971
    0x110a031110140f1803060c0a090801050105060f0901021905030301060806061204030f050903010f060536040305092e0306030309050603100e0a051905070509010c15020409 75
    0x14112842d00d4108411448010380420300c1c05040c600c0d030b50800d000316040d030f9000310300b11084035802001011102c507407621300000755041d440a03001c1000907440a00010708180c050080d141070364001403101e428082c05454540945d000700b41d0080c110300c0342d202c4108200c020030050030348640c0034402943d42c9604000e0003510515014260314019001003110090042200c124542c01a5240c640954100f001ca2400c8440b0301900d14000d07455481c00d059205000f40340d9000360120340056603a0b9031000d01078240002c102c000d6120044401100001100c080201c4001041c0d006110f0f0400070306100b0a680071442e40040c900d40140800074406500300c0d1170022416501c0c0000241c941808820f08681d802420085107203d2180144001702c04a068006507468000143c48500c41c03a558a291030017042e00980800d81d40a007181602c5410b0003010502d40c000e0358410080e90315180d18003400240115007410f908d100940d40003242c5910440c110b03203540000e200400c0c4e8010302040c4061914007152 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 348231438 1250 348230188 348230209
    0x40b0a0903060c0921060219090e090601080a030e0a1d06010e06130311131b080c0723010e01021602040f0e0606120102070c15030c0306081009110a0311 67
    0x4003030152041081015501240e0303480641000c17a500c502124000b4900a0042d0003424021586c002a000419901d00e074440c21100071565842d0021100380c58a14580b40c4401081c040c2c905103400680021020a0194038082007001c07000d000d020842c0e54500c903125800020005641020303c0c440f040c004a5a444500816104801c407021454604125456202c082040c80002c003a030141c03840b0f04c01e13180d44d51801c0c00180c10000c00c0920500d51402084442e4141200815004c11a4034000c0707901c680030070040d240300d503a03c00441c012010440150040300b0042e038450301c195640710901c20302c80400a001401d10740e02951150018441d1034810001594071b81e1a806209902e80002900d102d00009241e542042041e12154080750301c148c00700e40680305103880500940d07107140000514606103000900004920356041100d8560f41d4400c0b02a00d0003842040e20550103403050044540c10703507101840d02441504614092014480401c5211141e40c0c000d4607104c40c00c00c1c0101d5603003000803402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 348232688 1250 348231438 348231461
    0x6050c0f0f0304060c06090614010f06050a0e150c1209011b050a06050c0705060106090509060d050a080f1c0606030606020a0b150a030b04060912110705060d02040b0a090306 76
    0x60200031100744100d035607400341d4460355041240544110003400550f03441900c0603500311009001c40d40c00710280d4003000d0741c2880741c14080d1005000024a01c1e205400351b99050040e41e440c00301510f0040c08010200c0820504e003000540108151181c010741007240c880d01c11000b10035143c8034011040050910f807420b41c50301d09c00079200f041c0240050000b140913414ac0f40d03c6540000c0341d0303c64460000c494081d8100060031813041c0700000ca1941d070888020307821580c0c201d032282510303039a100c140900340901880040c8180e00c54400750000400c1c40015040c503040da01012400e10b940202d540000f0150310b034919002c695541410710400c3d034180503d03c0541290f00080040c401e550351000085500140003c0c82200d02140c2c4001c160b4a2103405801190030036071107115403c11742003c0000b4202c005044689110302d0074914510b90040804a0b10789411202402c0003500d00814004130f0750103400c244120300d500300f00102e00700e0031140c054415201141d0302c0245c15403c61400a0850b1000542c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 348233938 1250 348232688 348232693
    0xe03030304050f0c220c0e0d050105010e06040b03030316120204090e10060303140702060405091e060f01090e0c1608130806010e041e0203030d270803070503130c06050c0f 75
    0x41241e0052a4100c180a00105c5040080c003101c1c5030b40201ca560003000c13000740e8410302000c485400d02005411440c161840c4450b81c00342601e580040108407245001015050b4000b440016581355180303202440c0c40610b42403030287c04201d03180b110b0480e0312541048444907510710503140741100412809050803203e21040100070b04544020b0001050107500e8004000c00054000c115210081610020900074046c10392a082052560300520b800c2c1160000703084000d000102180340c00c94a04898540603118081558104011408140c0b40100400080709042241614202c2a104d82c48455070007a04090b884886000d6001c415003150b074403051090340542d00501840174500451600680c1c4a06010b640c852502800c03034400510000c00b80d4103000c04100c00000d4011a0040c0e1882502896141d014010304462142013058801002c1e01c200000d0001a13007143c050780040d600074190b03843c80c4000d0350031562008900b00140d00541d000445c04641ca2103850300c02c00201c101200c0c01c0d0003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 348235188 1250 348233938 348233959
    0x1814030f09240a1e020d090b0a091a070302100603170d0e073503030c0702030f100f0b04090b07140d051003020f06040f0909030e03030304050f0c 64
    0x980d28068003541903064030401842100c500a1040c40303030a01c0040c80e00c088225160341c0800e9002c0c0040d01e03481c215090164649400d0502d60348003142600d8068582d458a0b00e0302810310220050a0300f0040b218000d00803186030100742c4413a0014000c150b14125408990b03103520914000b403c108161101c150040e00b042c0d4148001036405002002812020f038843d6111008d03000d003180501443c9210346040c0c0684000840d04503069010f10885d10203642c065003c04003105070014044200600e000119041480401c031f00c0c002c00001800000e0005044600c004004030321f01d81000301e0f80d0100e58101d5a0b40e40803100042050280c5030951004450030000705180c1d8032039002c8010010f00401c00c1040302d1070861450041c0c12300317407414072804640410082c80d040c800a0100700150005030710038441c1c1011800203103804011141543d1542600d101c000d0301e051140000382c407a500d812018071151440004003031314104041c52096004000403d500d40201d44440e041109441069014500944 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 348236438 1250 348235188 348235207
    0x40e04110915012a050a0512120105130207021512130b07030b0102101d10110703050a020a06020703030f0b090105010c0b2d010e090a02181504181403 66
    0x201d2180084000b03090400f501300401c0c0000c00200c000f0110074078011618000c003000c1c0030300050f41e07240141c402d03402c8959003000395811000030b000745901800340d202d56000621203800e100c40342c901d803400d0310b41c000b5061a00590010b03a43c44100100c2c842909408240e4248110660014a800c04040b6483c084c806665494800785800001e0041041c5615869020580d03442006a000315100700002004400000e189001c00d1151011003821170303100c0c2c50300d88040c0b000984102400400d01480092804040780ced01554550020310b481015030045240c000d012514078002064218400d503000500203010b041175070101d0f01103915084c00743c03400b440140a01c1e40c202d00d44074805078108010288917500c0e100d141070501740c5402400b607081142d803480c1940303021442c0f05506980c05201e080429030381d100748060391076102800107540f00c50001440c4031100c0440e0b8480c1e8000c8000701400d210070004802003405d480807200020056181c03810700c00e00340718a00c4d000300e00441f150700c0651702c2d106480 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 348237688 1250 348236438 348236461
    0x212010504050411040e010603030311091011070f090501080d3002041d060109060f0905091f0b09010e0901050a0b090d051603020901051801140f06040e041109 70
    0x502400307001e00e5440c0081018860302901203425603000800c00d00414500d02d00ba28042c11003403004070046410a40c1c20702d2140750223000d803071103410003802a40c0700350451117088a583d9060390314240325000d00c1c500070540c0c401d0001c43c5c0002e0101507a000c1095407500300c0c010718003e0f03084048000c0013a5880318101c000c201d1452001c2072003e1400d0394130074241c2c0c000f0881c000d210359400480c001c0e45070401254803502950081e4452031098030f48072180c81d43d400090381c0301e00700030390740e000080d8491400b84064604081000e0300120b00c0380304c018aa070500725a00a00000c5600312020220b00400c410317030369681c401c02d03d0048800c282d841071215490400855030850340360041ca17208000c01b2030380b10b603944c448500d140d80203504039044408403d0000e59803103400034103001c181c1c0114200c81c0080b905060221004c508489600d115110582c6030102c8070201e40380c0002121b500034002c8004010390780c1c418001c0c101504000c6a14100303400d05241000c00302c1020b1004c10b00944040d0108010045070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 348238938 1250 348237688 348237691
    0x20c0c150c0d0e0406051c0b010f030c0302040504080d090308010512070609090e0f1e0d090312030c02011806050f0106030605130b03070509010e0712112d1b0606040212 74
    0x50700f000014501d0007070008014111030741206801584908000340d126000802100f00c03180508035581d03180c1d886210702c01d60030101e400060011117000034208018102a4072641e486405100e8041c14040d0106410341500c44100c0c003600026650001449289020300002c060150f0940017050141d180420150403d613051281c00800d69460300d524546c04030a1003024010386510007614403420269045407103410748a000519980304070203d0301c6080b80500300942c20780381c21400702060060480011400f070403140003800119501d81552a4200418034503d40c001d51050b400401c0c60300e45030050020b4081c059204508040c1012000c00164455481c0100501055130700070503405c401c000402d24141307140c3c3c402a00003a030040001040f00780c1810340d60142c005541d0b11842015840402c0701034030424805002141010811303502c1c038003241c409100d03482802c420074200200d641d44600c2229042280c50000d2400c2d0b82c004410300e000b0a0050f940c0c00002104d0850401071406086c199a400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 348240188 1250 348238938 348238963
    0x30610080414010e0714100c0807020d060f0b011b120c08090907030f0506031219091203030c021905031b01020d0f06140904050d080c0d020c0c150c 65
    0x100d18010070140480c0c014148001502d400090180c5920001e10580d5001ca40c460000c1ca1140b0080b070030b030946005401c840c400a0107680c2c81d401503c141d22801ea003640242412a403100425412900043c07107406401d0801e06000b2000942458110001d8080300710500080c0491400100c94000103ca003086032a5606c0c040c03402919608d601e03d04100710b84680c480d0a1350007006e250130000b00359030640015a45c0580d0402c280310a4032503805055031100f00c1c0d098140a180c01340300d000ca80400704503c20004400f1381c42c05070300d52507548031941e160100e80e080540c0000c1e15450f0b40c201250f010040507491000d0304100241d6156640c030fa0903164094002541d05515051002e408903680c02d405440e406070503450204001a10008004000c100c1403241c1c054a1034682400c290619101e03070560300c1590010043c00b40f014020074100e89041c80180001003004042c0501d4a8122a91000c0e1020350b0302c040c01001c40100741c0041041150410b001042141c6e0200400112420042030300646400e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 348241438 1250 348240188 348240197
    0x12060f15091d040c0602150a0f060909082101060512070e030d02061503031c020d06030b010b18090402061b12070c090b03030c0a030f051207030504050105060303030610 74
    0x14410802107034078035410380c040c001c5200c00b20381034180c100109242c140554810b0181c0503401d55100c2050ba240c0c3c41c0c0d029950003030700e6220001140c040550300309580c980301e0ba250000742d55403154000c404644c05480240c0700c80e01c000c240003034910205500c241c0f001c419001c810340c00e5858020020000e216214000ca0444510400701d40341c180030303680c58940c01c2802416074042e1013000c031000b50740f003030119450740880b9050410b40c0010700700402142d00000c2a0003d00c40da6003040d041141c0a176200d20040d01816584060010115462042590280c0026030780c035940c602014003c0c0f4201044c0c400c009101e200c6500074000180ea545040300d00709a00320240100550301c0f80060b0f4200154140c41c1e6203490f0300090040308100715850080c05170b030054a4200910581c19040c90303036034041c1c8015441c0d00d0341b0040b104408240a89018640c00c00d480c5401c5140410045102003509402d8522038082901e907024030041090078091540c4c440310540046045d440d2240020b840880300c0f490b00d40920 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 348242688 1250 348241438 348241469
    0x804090b0d0c030b07020615032a03010e0d030c050306010804020906150d09140a0c0b0318160302090f06060a0e0609090103050a561612060f 62
    0x3510780e40c103103200312900100104070385556802c004d404031404681c0a0300601582000400049410401015240d00a4014a52015a51030b40e25516180100e0703884600d00d503410714a02c41c0d03000d01428441e050490040c00314100402d00140c02d44000c0c894100c280311041c010418266400fa00507070b07002d50112105201502c030500828601032010800160003540001e41d41c0403003009030040100c062041c003076104141e04800010352039546000b0b0040c00105180004c129000d0f410b000380d0341020006001400340810180b516191003001150101ca21079031032000c0080d40303001034499511050664542001e440c00600080f180c3c0700d03107660103041c4a00711091050700d4071100c0540d0513100014103845410758481c00d00300d0b9500390302241101d4100e422843d170000001d0101c500c5a490510040e0301d03016007051400c2c004245d04010036101030143d021842d98030261021b0070035008803048910102003000c801c0d4000c094101c0f420081d51500e041540c10081d0149070a08101150301000e080a00c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 348243938 1250 348242688 348242711
    0x916020c06070201031803032f090907020f030c01050114100c02040c0504030c14210a171c051005062704020c0d08160e0315180f0a05011404080409 65
    0x2802016591201200d0b400200710800d42c06501191495140034011482103030000400d100d031000c800514440c0c103d00384008ae0a60500c07450440c0c0000403401902c00b580c8400586601d960002400b01d200d581d1500010040486040f0301c28100031010349000303580034032200c8080c1030029441c1001b03010b2070703a41100b40c3c942480b540a4138051a4401c1c0034050842e6074181a041d0300b013800c0c07a00c5204010008010346e00d44c01c0c80c10300008040180c0050184080b40e5280c01203070030415400420142010019414400400110303080300d5002c2d0000010903045c456501011900642c110314003a92040015591c00070030301c030010910303108030503031280d6980c1c0040106005e8002c40414500c1480b8000d00418042c0d00024400d02c0344140103c0c101c208007400b80f0032a18620390300ea040e038142d005804620603403101c4100181e405446031800c0d4168102010900b071401c0d182c090a4000e03034020b070b0408000c000080c003c580700c00c0c681a40300445814652510500341c0305a22403626010760380c090750b452 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 348245188 1250 348243938 348243941
    0xf100201020c01061206050903070317150d0308070206010503030f1c0e0a0507060311040e01180b0603071d1206010506031308130e06041512030207050a060e0916020c0607020103 78
    0x6010080d18020b0002e41e9641000380c05c00a002c45080b2001c0d030500000441148001042d0740c4420b4251703881450700214000c5040c007498000d40075442c00c1c1c08036076407108242c03900e03524903414912076a00c1543c41c3c58007550090400e881038011601c01c2c0c02c20803029215a031004280c409850307481c40600c070201d040070400c1c1b005150008030781015000d110082010f0040c0842c44d074080304c100e07480611030180c2d0410710740154443c074004c1500c2e0004080062000d41d404110005804101d81000030342000081e000070350980045544000241c0800701010720944000103940d112801650607101c515240703a002903c030503050140c2070140c50b0203c006200300902444210308590404145503444030b0040e5100900f01c041d01610791000040404a00c550400f4481c91040f01c00300c0d02c3d550340c21801c000914030883d0f10824254110300c1981000705035a1ba600418000601050f101c04000300d01d420f0500c101b0701d200a02246410629088002d4a26004100c1c5110001c0c2110728a560320a2480182c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 348246438 1250 348245188 348245197
    0xa0e0703020307060302120a091a040f0b010312120207080403120c0b0a020d1802010210020a050d0f0b040b0d030f0c0c03051b040e0c0d02150f191d0f10020102 70
    0xb5418881c4040000d42c40c0d41542c000c140498905019a01d03940c0c0c4c140c21a401e031065007400511000e00c0c90b941c404040e00d40000b464009104407a1491a0041d58494400580c000e8000392094090340884150150b0011000c481c1d120400d5415801d01c049521502814001c921020388415120950741e44298445c10202e0a0f440c3d0195819030941080140d4030029004031036040071213450300400c0501c901002034003101450b0305900404500b200d0a40e20741c0030750007905003138041c0b00c030511207444180520b000310520b0018141001401e00121f808200566802c81900fa0040d030380c80d03110401085d401107540c00c0012090a0010102c2100d20708003200c455503510203081401202c9040c514425058111101c601d406c070750903c8a04a00c1c44116180d52300d1040319644941d04034590300c0103040c4088100401810076140500749600e01202c00c07001d6101c1003490f00702414040001500980049099160b028060b4210610b0303010341c008201c1182cbd159000d14420300030b00024171401c1e4801d40440d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 348247688 1250 348246438 348246443
    0xa0f020d111309020901060e0d03030c020102090307080f1006030c060503040206090619020f030f0a110a0c0b030117010b130e071a0c120a140c0f061005030c0108010303080a0e0703 79
    0x4002c0407424021080040001e104200d10503205500001b46d80c600c920450980d008008010b000d00311299501500188030340104107080d55000c2c88542c02d1a5400d011070f00041000002420304400000350f01810129a9207104041c0d5140c10070a0005ca01c61011250a40d6024101142d0302d071600d0001500700c0c010304800c10b40c00f41001031042410625200040704203031141c2c0841e2038031510149140d40f64040c0381c4007100024800c2c44108891031180640250540c00481510001320480c0ca43e428104010f810610324a00c0000c01082a850340345051800d4070900c0b0f000b00482d80c0c2c00c1c0d001650303820300110344815842c0c94007c0051000c0041c000d0070002c20719651882d0224124852018941c1c01940c0044c085000780703c01000e403100201c0407610000c0e2640d4540b0303d2030f04245980e00c240c0c0c22003840d1050354030410303a00481c841c5040002e81d010b210300388501c042c0d040c580002c240c60030100c3e151490410090100420009400c503d00c941c02c212100e801080e82ca0117000141d14081455002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 348248938 1250 348247688 348247699
    0x3041d09030412230d120b0604030803090f0609010c020705101e08160903050607140c030a02100e0316060509240405060105030f030307080a0b100914030a0f020d11 72
    0x300340410158000444103c0440b1000e02d034101c03100030310b098451000d90705803c041001031b940030b07800004c5603100c2516040000c1c07101d0f04007070b03c81d211141180c104132000110740d480504038000d5140304005896005106034001c5c414980e2004000b500c4811512489004d01c00c07480c10016054000e00b0b104d801101c501c10064001803000c0c0c0001c00080b42919a894500c010500038404144554680002d680c3c1090081c00075842d00113040b91042d41c1008a0740e40c152051081514002c0244024090b0b800c450380100713641000d0400600031284122564072032640200f10710503020603242076509410b6000b010000319941c4040040d4105000c0a074403902040c405040c00c4941019401550702a0740940c003101c40683e210024940c0c0e40b4015010501c007580140000744403217220750011580b1080d1003101091040c04540440ca03c4c0030b08040b03079004200c0203842400501c040c06130080380c40104030010000e21a0f55256281c241d03c9641e00030713010b20140030840e0240865005165140304c1d02400c1d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 348250188 1250 348248938 348248969
    0x7090213120b0f070c0503070f0215070308040c090c0807030b150708032502030f0304020a03020a03151a13090204090507030f0c0b07080306281701050903041d090304 73
    0x912a030140800c0f01c481845002802c0407075003d9100d0300c030540d07885a00c10015441d20003181c90307100c280c0c005020101e0340240300f00e840c1c088010150010f418164030075180c0b0341031030409143c48160014130f03800c0b03821424501a8100ca40d945d1100c0384c2a0000c807141000680251000081504000c0e010140346444200003450020012048000c1d4840c0c3c0c0c95280542c540000303100195407048211240d80010707030041c000766118501110045070024402000d0020103682d0754049002002c148e07105480002549201502d4046580a4200b0140030190044051541ea90000700c640032129078940350700d6900d0103070004549407030b4007001c8103503041000c83d01120b650386800c2c1e040303603000581100c110710780c0b04000030201c80010039160303195841540c850842d510601401211507448101420b06d920b94080d80307001709402c0e212403000e42460045403000780b518028403030a56a024100c102c0d80d5100b004104042c4000800d01d14001d00315803808080c68031490211303403442c0075581244045520700704 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 348251438 1250 348250188 348250193
    0x60f0627040c11010f0b0105040e18100e010c0206010602121c020d050103031206152a0b0603010b09040c0b0a120c0c060c051e0903120c03030a060f080709021312 71
    0x10320320704425200c3d500900000c0d4818101d1010388041d6030805000c181c00380010f02c0280480c150440d40300f00d000d5007881400303900c8080710703107070494050182c290b00d0f55803103802030700d00ca00b80510819280c450009200c954502407009541c1e1000d00303941c401c0800040b902003080f03201c0042c54451906022400d54503000c44654140c0100001c0c8000c03004510840c4150b4420f2909020340701c1201c07045541c03841503072039411080d142540310195041d0403c080c02101c0c0340354203040c114544010b009902070301903840c003d400d1500b100c5c141342d1000d01c503501c0e400c00c010010700e4065550003595640300c209030f211180310704141c420b200303880e42d080401410000c1e00010158400741c10344c0094003c0c40c00f40075a90400030142d4032485611600591051080012440325200c2d1000340726951005d0101ca001080d6040e1406003070300440c1000c41c45400020500100c1c8459004e00c4003c1c225107410000841c0c07402117180e9a5880303612500e003170207401044502e90003040c00d45030070080c6062a8507840780803d03071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 348252688 1250 348251438 348251447
    0x50309120c070503060f092a04020d1406060909040204020d1512170c0a020d0201020319030902090708090a031b170703020f0106060203040e060a030c0e0f060f0627040c 74
    0x3409844d01070711801001444014070706001c1e601580740c4074040c1c031a00400f10818100458051855000402080c60741d00007030b00c0e248014906005107840000d2002c030452514070705500050700e902c4c07281130103012150781a610f03544903680050341102c00680e91052000240003a00c0040c40000402c49050780005c1c40810341c4d10750700302e114805c6143c2c1070643c1140c83c40065034015180a14031580c07220008030014200b4101045841c1d00500449081c00360150400b040d180307800b89200d0000fa1103845071000c600704100629085402402d0141c10ba140c0000c1c4a44e8948038078101808210341c40f50010038070217241c4007003101150010f0002050075070300c0340d40d041c07660f10840040300144140c4400072400c64040c0f0036081501c2d200c0d4041d616243c5001c4075072081203405004d00e5484559003500000003801e0a09036002003105643e1350707131980380299802c2c500c00d0000700240d0040300d00c080c0102040d5514411110858565038203658204802c02c1c41c581414400c1c1296500149005480c0c107103540c02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 348253938 1250 348252688 348252703
    0x302090f040e031b0318270903130806061005071e08030f0709031101030e01020903030c1c050f040b030a0e100219021203010323030d020301060e0d12050309120c 71
    0x10000c0130400c0400c0d4180f181d40d03900ca0480c05c205400390341c030051481494074100c2d070364180c84107414041c44c03610b418048900c1800d056485a20030f50000551718030b02c1c00d56203a850010008400940308501d07201000c101c81c94540c0421000f0440c00243c00410086600282910400c8484d10280400901d24044c0401e80c02680d981d64201041e40c0011105807007140010f017900c0d48401a41903207041c070b20065001c0c00040100c6440c6540a02480340d044e02d04001519005035008010942c4262240030f80741d211815003403160401c0000c01100030070310500011141141c18044d0130690f01e6a0301745000009140c61102c00321030740601d041120750314801d500074001040110101d150108581348040e0f03600d042405500c951200240010004a283d401c02c84128042522540c19a200c3e0109503030b0650b4130036068200300981c04030050020b180e000c0b03000802d020080e030340b17035038051420703200d0140604456a02030100b040001c006040550144000f1071920444040c0c1900c6100500402c0c2d20f400c403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 348255188 1250 348253938 348253957
    0x20d030506060c070b0a050702031606030c0503070c1b0518160518040c1817010f060605090d0816060f0b0103090308070e0d0b012403020405010f0302090f040e03 71
    0x1000c0105825103041400c4441c9010380310300801c11507240254154583d001074034800f003880010f100348005070f00c0c140f01c0c201c4022282c22220b0111814031398003900700c0f0010b06025040102c14400c000103a07230807004e00400c44e40c03c000c0c40d0901c10045c83c808011100a90405500319058940340001d01c06810510740c05100032000300d10341445242004c0f12103002d400c401990000358000e00c80010308080e803205040c510246844030080c50000690560021540c0c48040101c16400a610504400707104030004500a10030078840d0341d19002008000b4080c1001072440b81c00909254810000309008603000116043c1580c0d10f60720090510400078004003d80701c140b142403c140301c00640c072030312a5042e0f50768551501c03880d50310751031000c840760143c0780f40f0700360051074100e1544080b8a035520030700c0c000c02036903d540c1c01d508420f40041c039602800041440601d801400280410382c2c1000705030044840300d00d4010380300d00250002410130255002c0387d40e00b0515203940c81040f180040700400c411074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 348256438 1250 348255188 348255191
    0x1308030d0c021b010302030405070302150c010b03011a06030907210201030615200309150d0c0c20030304090906020405100c0c0311030c0a090c0e040e0303010b0f040e07020d03 77
    0x140742000a0707841d1100914030030320000401c01d40140940c0254081c0d034116010f40102e4242c55160760216a60740d00c00d5003c049440000b140c5c032071a049007401032048080b0164000c1c007a8102064006040400c40c4030540e20a40c40803000400e4030700100080e00c02024160700c011241c4410a01001c8018240502a030002e81003c2c0c001c41c8103058440d100b01c01c10b0140d910385401070315582e1200b020240c00443c150450008100b500d01c66500c4030058100803152040c40d03603540040c0b40c5503500312403030301480102f442102c2440001040d80c1030b034400c007040103080b11005150300c00d0001a05622443d04000070541c901500401032040c40c0d8003030010790f681500c20001e003441505099846034020440145018011030301840003441190003806030100c080d08845101400303000013014a07425400c0891065950700b82c045015074490740e06c20190600355010090f010b00c0c0780c03d0075124441409001220342c00000c6440244403807900302c03001000700d194041054103100b0340c025201c03c000340300c20740081d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 348257688 1250 348256438 348256451
    0x33b0111010b090a0207150c08061e03151e09070e010f08030412020607020409140d0c0f140f0d020c130e03030f0a0e01061403060a020a0918021308030d 67
    0x240520580b0300800b402042d10185580f00903416002e0b501a98007105d0310302c80b64211804001190050f4000c044581e121403080d446c103074092000e030804a1080c4c1c080d10402c0c003141c03031150320700cc2080f4401d42c1c40e8400c12070301a520420071b05844628446d6024504500c081008102c1e88003103450310030340e130820107400001c1e42d80d03901004d800c1c0706501825040b500100030400101305a09112080103101802490070290359400007811603078101c00c141d4072504602d0555074940002d0100d44161b00e0642064010030714580c8802071a84170b41d11005100014603e01015100350030807096820300000c038201e501000043c08000d4560702d20440340c6002e180f584001d51404500780c018403100c0803014004505541c2c40566840c1d100401078180506a9529541d210741d02c803080c003030100078010000154501c0007a690501d4030300708000f00004000e52050007024405a40076030803500f1501d800f544d4082210034641600001c0c810382050380c078500321400002469100c040060310591800d07440401c80e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 348258938 1250 348257688 348257717
    0xc0607031d190e150603190b0405130206090604320a06050d05060112111201210b1905072006070f2106030803010f0b0c0a033b01 57
    0x1d120221804000140b80000a000880400e01107903840240d00302500681d108080204445600070340d0800031803140c5200b06082e015850181c0c101d4104283d4080282c1c1c500013020300c509090000c2700a100b03410000d9002c0d000c1c3d40d03120541c0d014050402071840b148051030011035020043c8185808180405070307403900c0c90702d00810545c0440d03045448080c54000413210ba100240401001c141c14061501e207698006607052180d0710700c0c0301600c11041c0c2d641c15410b0b00e001c203c0e10140c0c800402681a0328500082401992084942c5a84601071a40350b890320519290481ea0341c0640f800d00310f281c0010400581d40c851000105502420341c648806049a294141c880f0004c031508804140c22403a4504c0c0342c2e2144401e40800f08224014031080c8074503a0f0308038180c4807581e04c04e8a1021010006100321068503040350001c00458594502d05001100341d00d440d00e03494000a000c0c0400740d507e0000d5400c50035a02130342e20310180c06980f02030f24004900568800c4444107240000d1a05100441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 348260188 1250 348258938 348258949
    0x5060a2106020904140a020c0f012f0f070503072d0308090c0303040305060f160903150b060c06010602102d020426121204140c0607031d 60
    0x241000c000d40842180000358840c40040d600c200d82030b942003595801d81504c4060030503091806204981710241c3e236030460110483c0303416034142c2110382a03450244a41a00304103515106448811104039800f4108195032001160044039003c0c003480600082c02010400701000508405104181d0210050b04207407014550b000c2c096a804401c14070000c0f56000b10740a0003104e5880362002d02164440100e17100440e085411580c002ca442d58854400d000d1401480e0110760ba00481c0f0306100301c07040141c41c100400c120814840608107607041c402c180d654550680025900300301c00340009907920010791105944510034414140140901154101c0f214024000d0305801c640311582d40c030001d0903008186180540c0c42410300081982080002042c221400c1e0b0300509281c6002400c030f42e0040c00403898180f1203008210000140f0800005800c41500301229030015086016440782c184160300c05450002c4100c0203030350042d030103e045410168024240c15101c40205000c070205c100103028810f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 348261438 1250 348260188 348260219
    0xe04050c161410090b06040b0f0109140a120f02130b130b03010e010513030e010305071b0f020a12020a05040203070207060807052125050901050a0e0a060305060a 71
    0x420404184400c0300032941110382000c0104070b03030098810510003489081c04686880100310781c484114420000c4625040c420999000d0b010f5483d4500140c656000802500a90150440080c500c45403198244c41e5200c81001030024050ba6203440143c41c02c00717980d07070280300c3ca0480c0700ea0849010210b0840b580e000b40c1401e8003001d0044282410084144030192000701c02082d0150b50362040c0418450303090003414094644401c00c883c041c4980e04004104005201926040c11300b030009028002c0d5010201c06030300c010100300004404060b10780070030032088104020350312041003c8007040c01032910b40102c0207903100719840030209079550248401d80c00116040070250300410b0041000f90300406c4035590101942c9013051404400f950250141c4020a6805ca01d0004040c10403903c1d041c80301e01a85113050845e0707000c103203142c10b0700001e15130b2080303403c05810001c010071107590f4240a0319003100d00e080010300400041d80c841c03600400070030f000c48a20b8800e12a0400c00a8080180e46001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 348262688 1250 348261438 348261457
    0x70b060114041406130f08120c030301092a030606030c0e0d0b1003080406050702040c0e030a03140c012910090303030b060c0f0a0203010501080d08340e04050c 70
    0x3141018544161007800c2d070f141c6003400b50000b10070041c0030b0b50b0054020b8401d0180880c822207801883c10800384034500024240030100b518001c0144d002541e10002c1524111004080003151400340e07651380c000c41180655034910151503940322071940e00d805400c207c040d20681c1c5d50411941c9000c801c120394404161a0b00c0343c000360032043c140d0101c2c909002e44c6a20401030001c81c04079aa490340c402129a000741e0101001401c045580001c5107001c2c0a03441e030040c22881d03c03220b04158440082c1d101c0d00001d42c002e040c044581240e0451800c640c080c0c54600e01808020030030810400000240e85410702c20f042104202c2491103446864a01110001c55010740d8030142a0703030950741c080d00200001c8168560100050102da141c0d04801c21000400c1103800020309462101441814203507171041e0800c034001d40003c1894448c861f4400b00d2254000d9002c00344101d440380b0300c1c0200100004540071900c00048181480c400650444070900c000300741590200040d5489c0002e0003028007450102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 348263938 1250 348262688 348262727
    0xe07051906080c030601091d0906070c0809310b0f010f02100e1c121104060e011407061104030b0c0310090f060e0112110301063215070b0601 62
    0x203c0e807020800300243d80d0000042c103061008503100d803c00e0810800c0d1402c00c5e00e05429040c01c0005081050000c990041c59604104100207815030f030703965041c0600b881c580d0248072070300201380e0440c00100550184000121020415400d05003580000d007402c00304640c096a142c2442e0341c0c0c2035104065800441e100c7d580a005005105d60700c1340c1c017400204074800e01e180308403c03801521401c4c1511601064000b5214980c0100d00c1c2c0c410f50701500c11200c1c1d84504100f040c0820090640c225808843c078140c00d00e0040880502e4003803100c868003443e035014060074034180329405101d40402c003c105880c05095480255945c40d510754030b65120848864050040400080201c0c451582110f02c800c40303202d0010036429200c05042140c64002d03071107027144052140319681030011035207100b5801c103003d40c002c1c05802d0a00d4030a646d0462102029281082e684403c0030300c4401140440080210040022a03000740d0b28140b102ca5400100702a90713505054030104060758044e0001a89121700c0408 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 348265188 1250 348263938 348263941
    0x30f04060c03090f2301090b25060c170f070e01080a1d0d030c0e06090108090a0609081305030a02011e0513080a2a14040f0e0705190608 60
    0x404a07107603101c03500c0031403c0c481c0b02100460201091110360010f0303c3c188441c0b805907202d5688446504684204c9641172160000060215220038000c03142540000c402110070790340b04502c2034182140f0b04102401044c90640040314856124200d803661800d5511a00441d8455811800102d1415200100400d811102144055010380d84032940702135020000034a0300c10b034000a00c0d090380c008124415039000114940b00c041c1d0148610461500c03180f07800c0e00903400c00d50208810303200b145a1541401350800000c2c000d55070800c0004680740d8040410f104038081c5203411010313500020740300d01401c80712190101b03041c18000b91850b0100e405035501c101d81c4641122a82ca0301c00401200c208003c1c0820202d40300ca40c4c01e5001c94010410900280118807483c18200091030030301e0f2120084c42a400000c207040e91030600d03a80c0c1544e04184104400e5a90900018010b080070010180d8103411f01a01904010300800c000381103031030075500c141d054820850b0340031069a81d03000e50b8000c14140740 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 348266438 1250 348265188 348265199
    0x80a06061d190219020d0f02010603150504020a05031609050f0c030f1f031b0e0c04140102070f180507020c0612100503030c0a0309080307022112040906031103030f04 73
    0x42c2c040500c1c1161910040c6400d1a029415005030100c00586000d64015a10f403a0790700d5105520420f41c0d0906d00c003c0000c00e05641e03c0510802e03c0e9040d0324002d0b40c0313541c0071409540d00d00c5200801001c0080803115816801080019a29028480d0310840c0c0d1030280010505c030354150340107110ba10452016459699420302c949030711200070f0312503000040402c100e204001d51503250400039600916105910980c544030038800008240c0090a29908440501c91400c00c500c0c00c4d98103440711408003038174450441300102c1c5003006079403044032580348100d0000340d001c04a400310843c1c1e0304a03c1e4284030a175910b0700240e949007450b060481d0005020425003800351140303040c00e030300010b410151200b015500c3c40081c2c40c0d900003c419800319007094261604060304444130a0003000c20030051030a000c1c0c1600002c1040790300080c0c841d41c4170388050311114119010b21003006201c104080340350302c51361120a4000202154002180c1d501100e15140d1121315000090310190401003003e0780c45c080c20503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 348267688 1250 348266438 348266461
    0x5070e0403080f0703142a0c03090418050a080d09081902010e010b060d09060e030403140d0f020303070c051005041103160513090f060207110a050d021f090807080a06061d 75
    0x1116900118401c100d047d0310009154030040c10440da00d04d00a40d1280310750000c100899241d0350302c4d0300700c01071500b41c5400060008140e091409802102d429120040c4401850181201d241d0007000c6210015081030b1503034030004034902c0403115500801c1200c80c10000c243c201c644564500764009028840c100281050390040c000c428841ca41c040344100c0741d040d2007499500700e5001144d00b85d04041d1300b5034100c031b410455030325071f0310541c41c0402141c0f5000b60007945038031024001404004c003030036404040c41020081016081c3c00b1307034020030840c0740030b0611507078190200340414440d00410000103c45c2d0b10116221060390002010315600300409400740c401840b039120110399030f1070400c4204000c0b50445c8041c1160302d000382001d409440008041142a038000e4022030703c04c0300031203924030142e100c201c69051a14a00008000324074a156001c1d03541c0310325a400001c4500c141c41d0702245862001c240b15403581d02c140b500f80035086d102c0e029007400e0700c0c82c45d80111448464500255140040c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 348268938 1250 348267688 348267721
    0x1502090105090901080d08090312070e0a051c02040c2a05150406020415080f040b10180e0f03090d030f090f0801050906280905070e0403080f070314 65
    0x50600c545014542d5000c2000d5802c05d074000c1a0507000300c0391b42d41c1610780000009501c410400082c502e0891403118000c00c0003c041c112904003c41c0a851034140e0f1210859100541340040c42210000714205085c82c0c03110107404224052130810125801003070069408910038a14000e8440c4080b90030721544030348180d07001d8191004c1c41501030b022a0760032014915405240a140050f0340c030340c144464101c0d0914184016800c11584800700100c80422a603110f41007a8451900320070341d101c5d2050b80840f2185a04542e0b5511150b02401e042c0b04460390064104005e504242c5c0e0114041526076a140c0c040c0c66811034000c2100741c580c1c4002441195001684007283c1021450302c0c1d1030701c40080305015182c0089503239039034402c1808038019007000441d501000b181910140001c40d00e4980c0a2100070340c5543d0300c080d446c0c0b070084080003018045500035080202d82852070f4545401e0007401784a0940760b8030036214800001c01e410901c01d008004411200242d01809601c52000c07000c2060517 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 348270188 1250 348268938 348268957
    0x61b06060f0e0a0e0a081213060c0e0102010501050d05060402011404090f0f0e010b1c02220c08090303040c03030e0103020706060b03070905010302041802030c0c01091a01121502 78
    0x50315400400c903048002540000391034410002c1056250a4009a045030304103584440560300c44031503500003a031000c040724103407001641c1180c040d0300c0e41d03507a003001c44441190051442d41000a00c0c0c2c0466805901c9200d0900260b000b444103903640c0c000c0c0400902c0155020b016500410002030140d4041c02d035030140d03141da801d0420f143c269030310030a0040b50b0b04034112201058454402e0800e0b12461b014405446045100821814000c4c0000841c000529040c40d011034034051102d00640d07448481a1603403207001c070450f03943e03107a4080044009291152030440426024000b16190000000581703106607071000b00750003c217040d0313107066501d078403802e60b101e04040e020041e06000a416004180c020052040825100e0500e003002404240207600704070b0401d44184400c110b00d0358800984034403001e04080040e540d8441410052082c40380d00c030129400c2d801c142644080000403500c642e02a080f0241070021a62134030500c071010b0103011fa0180401207202103905254510703900504d84e07001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 348271438 1250 348270188 348270191
    0x13050d0c0302040533100509030a02120a0b01030c080d020a05030a05031b0a0c05010606030c02070b0918100305120f1b0f0115090501080102090102030f090406050d0b061207061b06 79
    0x25080c070300315403140f000380d00700c42c4003c080405c0c0c9009401c21120b12100b500e0320b4207059042803000d03000b19944200156010380719414803140302a00302c00038409440344c20741051009129684a0804106442481c403d44403180300c0d18006400261000c038540c82d03c5540100918500708500728112440d030400b5080c092025001c01059a500044400130141000c1e5501d4852809500381025802c40c0c80c66400002418105507445058540c00301e0900140e0320040c403282d8580c02020041210032048074401c04d020781501c002d0050010902440a00b00d0307108008172a4902d42200c03c04410b0300451514001001081c4603890a0140c14000840ca2910800c110382ca20240303044150309540108404c121030604180701800f160020380100b80c00741500b08001d41c581244040000d41e00d108040e40441180c1000c80c41c0f244d280d4554000c030b4001c2ca002400ea041c03506050078484c0840000341c4045d0b1140c001d20b540d0311140180410b910007102c0d940c1c0c070f0742250034081c060081d815081c0340308105c80c4c05c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 348272688 1250 348271438 348271471
    0x30b030c040905010e0606011110050a0209040203010602070e1b070b13120f0201140907060f050405040606110d0305060f01110a1a04050618030306010e19080313050d0c03020405 78
    0xd4071a4450030740902d0184002090403038005100c1420203002400e19030402003141d141401880000404000c207088941c4001031690300c1140030002030003100c82c120741c0701c0e00000000800c158001100415a000000507944036151450300c0d07000c0d0918843c404a404a06005040c08910065107455110a00642d01d01c100001a5201040000164800300101c0d258841038240300c0c0d030900c42c81000150320390701d80031310f1305049130321613502e180910509040044225864070424030030301c20f841c02010041e009208a60721a50007601220b002d13082c002051140080a90006100c3c1c01160b001c1d080103025841c9101440004448900d2081407a040c184104524200003480c507100b281d40c3d5401520031940b4a0130a89002e40c00e00c20081d01030641c11144100c905910000801180d0b00440300b4200001e40762180400308140c201c030038400820f0041c0c85240018101004402030844502c0c056819881e291101e08010251444540c0501100d80c45c00050005013400c0d07101682141d81445003001e1f1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 348273938 1250 348272688 348272713
    0x50f010e0a120c05100f0608010504051c0207080d030614190306180206030a0603030206010803071101030b0a0b0d060807060201140c09010309050f010b0906040911330405030d050712030b03 83
    0x700700060080e03051803680c41d03900c0841a002c87c402d146c003400d00d05000780054100741d181d566948480d0010700b020081844030f4418560300030000c0fa001040c10405540d98102646030140040c14948a451009202e015002e103581c42c20440c40c00c0798241c640c56040509045807141e6004001d1b0f484103910003c84501100e0260303441b640610b20a0035480b4001c210181140342c02820b001040e0b2003400240c2c024003170900052070080250742007000a00e0000b071146554000124008200d41c410300e00e42c1000200d140038481d10303400040550791004102e13a0303450b580d100e040307080740d00070411641e08440f50070100d038044d200080146003070039051501242c00211511407070f00703291290a0500b040c2c2e41d1158404203a00b0300340812580500c3c219001c00031003810391078046d4a080b00394442c61094004c1414206d8080380c50b128445250001000518001030341e02da01d002a13802801841e209204503121080f185200740115040f007680150320f540040c0441e8000c0d8040c200c0c810031154075004115841c1130 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 348275188 1250 348273938 348273943
    0x1180803071101200c0f070501050d18060905031315020d110a05010e060703060f0506030114030a05010218010e040501081c0915090501030e0615011b060c0507050f010e0a120c05 78
    0x7803400500441da50340c0301905c4507481c003254003455800d00e41081c0b108100c1030b071b00007040d280c010480010128203180743c40401322000500c884000d18841c40c0c0f11101d01808000006414442100d5031010700c40382e00c038410042d150351038180010050303001d1020140c2c194414140c81c5031504400c4103c405000c0c043e5106400d413030b030003d00303114540d000508100c0083e0781030103140000c00e800301c81e0301151b505040100d51507201c1401150b40740c3c1100520309c0f450340c40811140d0022900000219211040c0c8103e80701d41100c1d640c0c80a0001c0d000240140062a107842402d0498144800800e01140c40140d030b40158001002c014060080c1203100044d0000440c50328410981c95588401c40f80d401e2000250454100703908038030700343e8041d4007044608603142003c411142002d080c50700c401180c007400c0b201c0381d25000b5002000c00d800c00e4140196103070090060191688120144c1e810202181050360889003d003010303015a1b4002d5a130715012422012a00400c0300355490000003a9607191074051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 348276438 1250 348275188 348275231
    0xb0319030807080c03010302010203190509090117010b0909060a0c0c0b0a05010611010b0f040b0f060f04060e060a021b06040305011d0c0d03050405090a06050d0f0501180803071101 79
    0x100800d44007400c0080d02640003901560002d610505030b401d6504540000f50b42e8003c0100c07005280003c40858200e840c0070348145c41d49254000d01c0c641c1c440da1101d403c018460705c0400e1014056080001204241c900078604a110b554040014003083d41c076000c5240242000303800250070300ca1851500070106401c04445480b9201006000c200c6500d4004000c0c5800c6512414001c1c5c3d92410654400507034852a0020010070222004151201d4890009502c4445990000d60103400021060030245148025008075240f0351505405022030070f00b132154a1140c500c00c600160071444e00f1400c0485958110382e20f200019110600703180c1c6a6540c5821290340e401c1d200400f200d00141c210000d802000020441c40f03090b102101740050994025209000302d0207958802e01c894400031305c056a40d40d0102d03006241c010000d42500342141407640360505480e130256800d500b05051610fa240d07101c40b00000b450340c40030f2403d0ac2d5954001d01159618050300030061655225010401d10f07154960381d11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 348277688 1250 348276438 348276443
    0x616030329011e21020c0708010506040f020f0a03022a0115170c090408070215030411190501050703030b030d0e130605010801031401110a090e0a1b030b0319 69
    0xa800c0d5151100024040c0c01e070f181401e41040700c840f0790110a9070340c00060103030030480c254483c2080b03070b11240c480f5003c3c0c0903206030820b26104410000569000c15001540039003016035081240a8844c0004400e034410b507400c0702200801004012940e6109078000d10348a00d0b000310001000030290188240b82c42c01d21b1540c601a0f450b2801540c0e00c10450b40414000d10381c001c01d1504023881c112405458501010542e442103458000103401c0c090800300701e90015500500304c9010f0b008140703146841b5003045d80e040e40c1c5008104a00402810098449490314540b40010b05007c0e241030011111984019400c80030141c40301842111031300c00304018003102070b2a40b107984c1050302d41002d001d01420681020202c0e40c2c01d10800b04116600104840d06680d040160003103030700d5030203000c1d9000d0140064401c1c1250b10001d4800319643d8044001c03010b4420000311076509031566140c031001c0d00d140d12060a8441014407582e444203019500c200c41030200907003520451070080a5040010f540d04405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 348278938 1250 348277688 348277751
    0x405070e10080d0e0a1502100207080a0207140105180409051204051c0b060607050a0c060801090e06040b070e040905010f020c0609070e0a05100504020714010e010204030206160303 79
    0x90140180c00e0200070f002c10f806250039a200c030500e0001805c040254400c0030180c081108104042e2442407182c0c0b2800c0903801025960b404840c038100d1040d5119046810050180307034408070700aa1030708064210010142c0d103850a140b0034007507000b8001148500e04d5401503442006400040b4140540c015400d00090802d0300c031031900d0700340005c610094001c00c85a003e054005400212541c40c040d40090040d43d41a484200919106203460001c03c4054202030b41c081000907036941c08680750741a40c002c0e6805025a4041040359130b942c0c0c00a88000308402c2400001515040c41050102c0d1b48040003003010420010030b40316107085400640059003840d40006e1a4500f40710100102c50304050800d0041c1009880c06092007007805014040c2003d180e00d4001080b40381046004200140070010000c540d244c03901d20304460b42240184180840c0d5091a020050702c603010f101f91002c40c0c4c0c001d03120620703040842c6007107640b1100d5200220f05155807020304142c60414418014030b250300c002030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 348280188 1250 348278938 348278971
    0x403050d021f02130b030703020906130503070905250e100206060a050a0f06121b0503061f0509120a06090b220f030507022404030b0c070314030405070e 67
    0x10b81c01411406040145000f4010000d0345220300700801c03003d0480e000001c9041d01c907124980118080c0c42285401075100502090404042002d0000e840840f542141140c60a6070b03184c0002d0300342c0710219400042c84180818246440c004007240c0c40340600fa0b85400394105082c040003900c1083c00e0704400006a000c0d004000703440c20082052005008100c81010020380303040c3c42e00b41c0b0000c0d640a500d040120070301109659108c00e8010140c07050845090399400c07400e22f40002c105410032138200c0c4c401d000c003003540d007503500100c007d0000c04070b2030790381700f07413401c840c2c102442035809001c107540070b2510030001c1c50000700c0c02c28811104003074030400403844030307090000340094546c921590410100049032810000200402cdc00a84810f5160502c1c0c1e40301d22542c00003640c6107008001078810b50a044e440119084815802002524480c0ea0310b40c80c5510790040300c0c2028003944c070000700441c940e5003c441c0e5000c0041e0195034054802c41c06c1303907589511000386a410402c16a1860101c015070311 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 348281438 1250 348280188 348280213
    0x20910050405280b0303092106040803070f110606060c16080a0c0b040b040323010e0d020d0206100302010c14030a051c09020a03060e0a140709110c100507050403050d02 74
    0x1c2c50f084100c00345410903c0002c0509000035100c7c8141c8444a00c40c0707412071304a0070041e5a41c02001c116504040070355a551416007000a2164811a01600060703481400d03400354900858620408110f004024900382d651030f403d0224507800710050901601c25010801c0da40303130418159801418a036001390020f0709103440c08441c40e5146800214030807905220134030006200c2020740e8200d03500078000f8036492034a82c00c90f41c00c81285a180c03c205500701055a0f011500004100f8080c100643c21918950500e1008a80b0f580069500d504114401c22080000d588981244440c090081c1d07070f030b8518881030f00d5100307145501030641c1d040440c1021911450540380745249482e680c202d8030303090001820f01e82c001041e510031800003d00050751001003e07000201001006c01c80f0f40d006026111403881049a10360ba00c50034818400c2c0181441c001c41d510700110320030f9501d840016401425400f21683c09200039040051048003041b000340030000c0420420049030058007029000f4011122542 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 348282688 1250 348281438 348281491
    0x90f100c02120304080a080406090f0302070f050301020909010e07031d060601201e0106050402040b030f010609030201121a0d1211060108070314010b040921140403020910050405 78
    0x40b800507003061001e0082001040c0382104540400100b4034104600d0b6403185405801002c44020203070000300441602002c2540015505d03080d1100d00b0030342145207644500b01030903442203068030798014a00600401880a880504941102440c2808120b08d0b28080c61203104404000c89000c595011505014503960425203c01030080000015400720141000c642d81c0d80c048014240c48403121514030000d421401c4d8041006094001c00030340d41c956446211081d160810b486040a6103400300001400728080c01024045035810b07160f80c40c40f6010b4403a0740c4010103420380301d60009a0b04c000f001145541d00c1c0c060807030f03141c406d8038a404900120a40100106e14904804009030b01080061014000020715001100d9010b1045454a994000180d02500b2007900140e00709042c842c96030301300042c40e412580e442a661144003003410080318201c0301d000c884a00107450040420007480541400040035034040e8130040001d0400740d940e0007017401c940048070a801c100c90780c48103101200d0b050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 348283938 1250 348282688 348282703
    0x8072307180506011e02011b020a061b02060402090910020a031b02060411190b030103210503040b0112031e0210200307110a050f01020306010e0603100608090f100c02 73
    0x9a5900b0002854018000703041c01448000c030f800311403040c08502261074400d422146400c40003c070079600d040c02040001e9070303a141c04070040741e0302e80c10018545641400c0030b100881003081907008241a4a0715004d000580202034500046c0380514815402401110300007441c1115103540c001030040c20702c076038844071103114001c1c90046410070410b120116145401d02019401d0484801085021005c0d6103410410a03601034944d5a402100000911011011500b070018099a48501c2d20b500d251003200d9510040b039000b002c4003420001400801d001041281030f9038800d042054000d11008050714240c20360902050040e81700c00c0900c10b08140f20701580064007104c0b00c84100c01e9115290000305408011f0900040001c40c020544061200f040080d4450350028107641c42810030741d108a020f94011210603000c141d241500001609080040340e1207a40395064201c5524282001114a50000703031960095109070a40342240ca1000c1c0140c450304400488001b941020703000380039050605 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 348285188 1250 348283938 348283979
    0x31f091803140c0c0906120601080a0204110a050f0a0e0433030308040227090106030b01061e120b061204140d08070f020703080a020606030c031908072307 68
    0x2c0a00c03420001c504000343d038044904049a00500302d80c1e8000c04240b038030790b03406125a41803044000000711800046800147e050007030b1001c0c03290b0501e4015494075889454544400030350304000c080404030540d005030031100624501a0070000103039000a058525403402051400343d00031b1120180d000c0c0c510030713300342120781c0382c40101d45156403000750403440e0081010340107200c0b60440640b05152803000b0064441d10000704542420162145402892640401c03280c0d8403810740041850341c040c400504a60550300280190361183d448121501e0441402ca440041c0d268007042c85903542c0c2c40302270000c07416100c6460016140604040c1031500350886045840c0c0c21901500304100e5100d01c0c2c0d25446466400c204104140c0300c2d1040340742911560020380642008950541d0043d07000c29582c0c05500f045040b2080c1074440400c15442c2c0e841810501340c0e01888640210001c0c00c803a01501300303a8020300088011810030180f9216001801c90315012503003100005000e21000102401c25003503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 348286438 1250 348285188 348285227
    0x60f0f09180702072d03080a08090105010f17011e090605011a040b0a0504080d0306030b160504090b06040503102705061b09101e0311031f091803 64
    0x70682c1019454820b2800f0b4070369a40d00e80103c5428000e5400a025440902040c6501c0034558074240a0156008619200001041d510128680c0181406090306a03070380303040b508007000d01d42400001c1346405041920842e5484d41c825402208441c2d042410030b100c0100042815a680c1c98644100c030016000010740f060a825510b10415280090310240e80b0f09110656681a2011041e12280121b130300402d094030400c07084150a46d80358208104a070b10842c40b004242d1610041384444400340c0a42e8000203a0600c0204401026a04452086c0101074511403401b41c8800100342040e84480640b1601a111514000c810015440b104c6401443c180e40341c00950711a92140d88501002c2d1101002d0240c400c1c1047c00c000b154000c55482c0d0313100400060036201162000340520794a0280c40d0340c0302d40c500e040203038018024080d5403503100c00f100704145169079074404140003010401c19400c81c040243c1020072480700511680c000c8890005500c0c800c542c807440c00038050144000801201c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 348287688 1250 348286438 348286441
    0x101407030f11040308070804030b130c092d061205060906090307031d060f16031d06041a0405030f0102040906060504080604060915090303050619050d11060f0f0918 72
    0x1020b01603d0036207902c20b44240e1758124a007461022402103400141a4400f0031081c008a070031050010003240348900c10324020556261080700c11180c0d0b801d4581c1c940032007001d80100b02a180141004048110100011003649500d00c150704041c586d030f001c80c0c080e0321843c20701a25100421407540d00491300307401140340250b503039002419a011041112000c10914078000b0055a40c43c3c16160101d2100685c16120038005442e0382c00f80310400c009401107164003800a01c044155000300000e06000b0300a68609450b2440d03039801e0b0002d9001e1041d00450a01011466980034018140f80c4240c140c0056242c0f81009000300c200c440961001080c00010401088a00c0021072020361242d0060400500f151847c00c02c1c6441414040c10b420116103441c010008040d01680300300c0c0039110544d40e81512018002081051220a004540c1d0260755400c0050009140b15030f8250032101c083c140034140702640301c1902c1143c0010f0107007031100798081380500079401c0c01a0b04106200a00c00f2500e4207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 348288938 1250 348287688 348287711
    0x1020d0f09030c0b250302070308010803090a0b070614090d030e070531240909020d0f030c0b0109061508010e150109080d03150905060906040905101407030f 69
    0x442c002c1034401458403100744001160a00315290141c0031407003603091404170301a0050001c000f54802c0c00c0c03c401282d00c11002103880d903000416101c90220242c02000080d0520003c0c0701c2580003003a00f103420503260410840301c120180c1e43c142c05008040024024102c83c48030140c02d0700d240c103802c00c480360f11803c1d08000d19a112660901e4a4500b000a2210405801c0b101084030304004512102107003050180680c410b005d48280e5148804944104002c9442c0c1c09500300b0b80d1101500658008809480040418603119040c4034140c402d0030249412186c82d0341d44054040c00360300c100704281da01d480030485000c402441541c14034241c5805e421960501040c0081c1e030001803e0303030160907003040c140542a40203107241c00c05000c500c2c0803661001466100100030b0035040c92400d001d407100c0301c4002046501030140c240512002030000c10650b81c0d15050000070b05407001c5c00c2c1c0e03081c8520724100602c418184204004400b040b00341e440c0516060a01405543d580e4445090036880d044a41c0c85 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 348290188 1250 348288938 348288947
    0x801051302060c0a05071517240613150e12101a04090809040c0c050c22020703030501230d020d0515010801020414010f0f080a06080d0201020d0f0903 66
    0x18140d0489001c2d4548800c41e40143c58513900d940000c0c40c510030900c0c08240e6030b0180c0b01103500441255a500401c0c18565000c9220f80d4065841c0b0000100c1151100741c8118001360000642d41c003d0145410405c40f500c40265110180d0300225800a0780401858042e034001440101c2e001e013560401c8080020303410055883d000c03901d02c1411282d80d005508004403d16000420000c0b005005000e92615410400d6107640400d041d50f200d41e01c0c00e21101702c0c05000300c404106203170300040a0700001c0d420a050095084100d11400742d814001e0358070b1600104507101401c00c103400b960b0006580e40c10400d03201400310b000000610074440b1203900c07010756910040c020003442d5040d50344a802c041e5501d40185061241407411348800d010b5000441c480e00c0540c0500120744c0307040051540300c0701c140300541e41406c00600c4031002410601d94121500d00506a00c4d8206c0d08401c00064901e035a03070310050400705402101401030350001441007069040303008880c1c4244080c002001000303241e680240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 348291438 1250 348290188 348290221
    0x60a14060103290f100206060906120a0602030a09060e160b03190906021303141507050901110705031c120612020d05010e0a0b06030f16051c0203030d060f080105 71
    0x60314540030305404041c40e100d4013580881e41002030b02203084001070040113500c9100440351a0b0041100200048052a14520328811066048040d05c0c0798540350f103d03030020f54001400d410216488040c120f0014040344141b025408171400601a60a03104107140b403a04980c2d170103000010400e10a010600064000440d190241c405001400013901d2420402a00412115415103480301c0303800010311031410031882600320140241c170140303440582346903800501500c2c503200186047c809220036500421500706070800b2041201c1c1880e55413070020345411000f484c0c0c035405e0300140110090700740d0041004100028100c40500034207084c1a040c034401f001c0642c0203441780c41d0380c41300172043c48020b51101c4001050342059030200c89060500c03a051541c00c0e200d40c0d0103481341c000420400c020200d20f01c0c6000300808801b1800c5480d0004000310089660701015180c951a04541c0040e0b8041005101e03030070700d0711408603c3d41e00e042a032080721a80c0d54000019641004104400c2c88200c2e003150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 348292688 1250 348291438 348291491
    0xb0415091a0904060e01080c1503160c02010e1f1b1106030c0f030106022d070501080901060b0c0a03170f1b0d090f020f030d0905060c01020c060a14060103 68
    0xe600c40410b44000b60243c006036003c214080740030000422600004680500401c4007500d11040308047d414130400c00e840101d81088047c40100c6c15103e215201d59141c01a1130300502d8412100c441c0340d400115845c600803502625800110310a4610070b400990b00d1030724800322083c0c61400c41ea00d03180d11085003d4050b130f00344907400020004400645103003e4900c01d43c050610180c4035070b15100046c3d926500340700c0300c204c1159983c1202d50040210001c7c1000640d004001e840400d16040042d55000c5002d441001c065480700004901160814050824003040c170004015007038960030003800b40341c40c182207440c021541e9020449030860500d00960069042c6c8078000d50f02a070310440c010310380034911031410b645052030101014400860a0001580d00840e01f14514404801c2055900c960105850020a050402c20011458804050000090f041c0005842d000741081d10308e003030800845043d2050703651084058100801c11601d80d038041401c0c2410456a81000740d440002001c0120a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 348293938 1250 348292688 348292739
    0x303030b06090a09020906071b0306060f150c0314070c05280e0c0409110717031303050924030a150f0915031709030c0a060507030804050c0603010b041509 68
    0x45a1103440d00021540c0c0300d40c01809c0005080480480400c2100d940d21044c0e035502d051140215108412050342030032101c070100d00140007040e48005a035002402c0c002030302407100e40800d62241840d06801454841c1c0704543d403040d128140f00401400b00c000d01000020600441384000da0b8800120090041e00e1141054400541c1c03410900d00d078500c0f80c0e4000c010054281011000125401c4014040b124410568144c410440340c2c0740c42c91070f0104590280310088211400400310303008400800031703a9005403c0c1c194201801c914164161001459081c03406000410031044e240544214440d500d43ca009540340c141c82e040240780d03140000d001c0c580340290350300c406101908100c5904001568825905105a007040d650b543c916004400c0c51402800340d000c000d0708a24010a0754001c3e6009604d60310708108090303c00f202d24410080c0201c0b10362150141d084c80035900c20f40614020031740d8842c06a9103606003441450800d400c010100d041c040845010f100e000288012404001c6109a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 348295188 1250 348293938 348293947
    0x180a110d0b0405160f0c050703080f041401020c010801050d0812071e03050105031f0f050703020a022401030803060d0c0e150f0307030b09030412080a020c0907090e0408040801150303030b06090a0902 87
    0x92148c00c01c01c1581c802441d00704001408200c0d07c44920141045502246450741c00f500808016601d03240d1010303000380015039210050056146c016950058580264122420000d0f02000122407075416289800803036000d001201c140342e1441d409540c1d01e41c075880c061103554501000700e03030340b0000d0303c54001c10f07492240c9010f407002013160702039014850401010721407030a04400203002580011200d80040c0214005801e040e00d803080784603070039548050186034a038a140c0b00d0042d20f0b0005014558040143c0800602041154030941d0280c00c244009402c030f410710030000325151100e03500702c03402404035a6501c1d04a075808075024045980100b40e81c41c441d511044400c0c210b01c500e40120125402001050007405280d00103400076420940885a821044204002e0340710300031640040000e034410000d1200f0001010100c0d00b0074400c1118600b49174890710060f0a60b100c800c1c090204403003110041040c50f9040c090303121902d40c20f5034110314002605000c030b803c0c05503034002d0800385600041c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 348296438 1250 348295188 348295193
    0x803010302130b181005010f050405060703090503150604050f130b040201021e030c0106090501050d120903150911060a0f050310030506010f0f060e180a110d0b0405160f0c 75
    0x411245503402c0081089a0348110305401e415203803802e03202e01100c9032005c0c4c004130340b9501035242c83c1020006502e929040c94a0700c003c0203840d42c000b10b011801c20071001000079668404010070a80d07006c00195208062901c0800d12040f1080185290325a07035400342400281510250754020b046d400c0013000540e030361035000607458003100421002005160300c40161410720084080d0100c08440784c000c1c0001c564a4440b501580c00078001c0941c003480d2004c907140000c4621035510b40c00c19481c11b01e04005030b56602d40060031386941861449268687d1821802c10821442c42e40c4400800c580c414181881c10300002c260f4008594800d061001c000040303070111040b85240303401150f000c02281c001703607100e15001201100c40d10525901c800004000f1400754001d4000e8040030b6405407000c0b01c2e030104c90b206183d8548005c0c2c5039880703c1d036035203c00c141d010f4002c4000300017040491002007010350f040000e000c105c4030020110741e030803400341d001680c00c00d9001d03000241180e814500341c54580d0050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 348297688 1250 348296438 348296441
    0x305120604270c0b030c071a040203060c0a140406050703170103030e040e030c03040b0702010207090603080901030207110405090d0f08010b0702042c0d1b032010020c0a120c080301030213 82
    0x15040302413007001c0841041044e6440034014200184500111030111021090146900e401510020b40c190801c0c400a0851000000a0500c0d8449803400800c1c0d102c004491101e10390140c0c006000140700042c0030424560000c5448500c007024408502c01d030b624646004000e04081140544165120f004140c00c200080040e10b1000441400b40e0784e03155600c094107005540482e10890260003003000009240400c1c4c405d00b8101c036009201c95141c140102c00440c025070003180c0496a00e1040342c068030041d10745200c1c2038400d058040060805005100c80a0038010b001c82141c0308001d0071000501400c025801520741090313050b640450002e0100c3c69240310445d0f0b07100200d00414000c400c001e20f440e000038081032600c00711749680414030481103807a50060b002c03000241c0400c0240c2038250140802d40303a10000c100042c015100c0001c070003120306007130b43e000c00300d081c6056100340d818006009180d0080305483c02d407400c0c4501030303085607650755400d40070512029101e80070f11701c45140f00c00d030103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 348298938 1250 348297688 348297713
    0x21e03090301050a0b0f09150f040f05070801091b0c0f05030c0d09090b15090d0303060503030d02040e010806010609030b0a06050603040f0311060c0d09050c0d030512060427 76
    0x700240100d25181100000801900d4441407007000d904400045505003100c0c980d01a0080401d41c4521005c400b0620030007110000c040313900541d4400c1800710404540c42940d00a0400c0d030f85c1c00520394503210440d4150382c0c40702441300000759141000344c0c0c60380d0801452140180c0c00103842e0f1510482d800c0460850160400b80249405000c0000140d1741e403042c400d00659036022000c111a86506040c007a0703000c40d504031210700b07a4080001c02034610703044440800d090f100e80380c04119291200d010a0558000201a1440300d4000c2014040883c138034004c41d02500c01000188400e42c5031440040040c00c00c0c0c0310140c03104000303c003c101102e2058001c20041c14004c3e01d0b9a660b810a85024403104020074015030019100300c924030140c0c20f020035406e02801c3d6100c1e0a43c105805126400010003d84a003103900d0b1080e10800c000544802654110740d900030340b1140c0d2542c041c004003030090384005100324403071803501608902845925800300e50b01060b9401000d003002161402c800c1e44420f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 348300188 1250 348298938 348298957
    0x60109152f07030c060305010506030103060203040c0305031605011a090601230318010c02160b0c01180506041703090703151d01051609050906090916030308070f050a021e03 76
    0xc2801c481100504005910411640b1821210500c1596000d04404442080c019184c0c40034040004201188a076009950000c2c0516884462240c0c0ca580c3c4506c6d6a20802040410020520001e804d0090038405e2115034443e00c158600c4e040b030500f0002d110301900030002818404448000300003107102f0720104032408202c1c406907949080c4031003294042c1e03030303003140d480400d6080000d01554a84042070210242440c25401e00c40141888a001559040704c8480c07000e565036003080b58085110b05613a0f00005020380003070b1503581801d041c10f0151501500c1016501c00007041400307900b6000180070403c8030307007003a80003500c149a50221001380828440e04900f00d10100600104058191300c00c4d809289600b61500703c1c3c1d0403015094900c0c1400e807044645c04110000054000e0070007110350f661000f0003000b9641040f01440301c600703540c075040c0c000343c00040c144c0040212154000158038100415800d001703003881e0f00303240c00940e580480844940e501680c5026542c04003420000d542d07143c00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 348301438 1250 348300188 348300257
    0x9090f0507030807152d0f020d06051c03080606031321030612020d0605060402041a090102060714090f061317010b0604060503070806061308030d0506010915 69
    0x9030349080070229600136100a5441c0b0745043c4282180400503c210900e451422413480c400d1086c18150028543c01da6a00c07010a9071106045034a9100741d2000341060f6044a4001130100d0410003845115200c40b1102040040101d509a001c00d401007040c9510420032103019940380c1c0e862402d07030144c59101c2001030900715410359041803201092400070402c100307903404200c0c3c1e698402c41c43c21030141101019402241201014003c1176050b045642d00001c003400240c90540d80310388011316000703e4110300074030b01c4001c6520b040660741800a150446003614095400402d5448180c8040c81403480b180d219000ca103a0720021a29140143c9130905d0204150340f40e80e6660705c09400d089120903050f40c00b59440c0c008500b20303d182c01c80a071303029615650703243c609541d01c610003602d043d0b90140c1411b600000c1444800300c2c3c00c020554a0015010b69805140c495401c101071405441010380030742c0c14012044418049c00c0c880600e454131401440c501314401d500300c1c180039800b03281900080034020313 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 348302688 1250 348301438 348301453
    0x705100c0507060f061404151205031903110d0207050c1306080601080d020a1b150906021005040b27010204082104080303071d0a08071406031009090f05 67
    0x7900100607020042c02100d040c8030035500d03482c24030304031002809400080602c800c04d03200c0f0313401c140c1e0014480302801d02c3c5203401e041d01c642e200e402065005a045509a1000401c07010b00f40e00c4d000c1c030b0311030751030a42410700008139540751640b44c40c02020b81285003542e0105001d41801400c00c0f44444400d00501506088101020305a0140c09540103602040c46204000950001d000a8050360b84940d83e02074640c1c03007056910306211880c01c0c0e0075268101440840490b040c0204090343c03000c0301140c0c4444104a2400d071000e814001c44c820481d0307601d880c0608110100d8280344003240c0c420b10044030540d001c6c2045011a0160420741d1890480c0e40c4041004034100000085003260380445041c549409082c8505000d031511407802036084a42050012500e400d00540e40c40c801040811103042e140390100010031010780a0798400e07412640401c3c0d0402c891090003001c4025402d040e1a600d1452030000455411078602d88511040340f56a4610b003c20701944e401c01c2542c440c3d019003959060f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 348303938 1250 348302688 348302711
    0x1e0402130b1305150d0b2b0308010905370e070518070e010e0a03020301050906160c050a020f0118030503030a180f0b18010c0207030606050603061302070510 69
    0x164100b2800b18207100c6814001041a14001000c0038590045040151410010300c10340344c05014880341c401d4110a0381486008905002c0204c140010300b00c41c4034101c1441c10381002040070700f041e40302840326032a000900c080b202d2490720a2405000300754034480140f070008507009814012801440c08503181c002c05c1084114041242811540202c41c400560160503041d01c1105174103030f0303054000ca941d905a401aa5006005401c101c072001000a4841956030b0080303400d4030300c00c41e40c0301a26000301d8204180100c1102000c2c1d9500c10b10702e01074803041070a565156030340d9480c0c40c01903c00d948000c03a03024145e2040c881a0842c86130119420005075517032412030b40c0e9800030303240062080c0c00c24031209240f800100c95031143c50f4108038488056103603074550300a4160007a02d840c021000382d807110b1200300d20034050400184107aa009001d04c07407841c203010040341d103190803082c441d1004009014243e65200100103000b6081d0f200183d5030041403030b0581c07407c10f0040c038001e4070a00784000c040a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 348305188 1250 348303938 348303959
    0x90a030f050706180911041a0901230414060417030c1b0d140a020a06020705030606030303040c0608091f0b0f09010b160503072012010b1e040213 64
    0xd84540102c4070041c1d200c072020780c0d11901000c11010260182e41c81000000070170b4104020583d0842031480c0350070344441c841a00c07010a00d250b22280b96000850b54555603011110759029480c0c01d00b20581c0b045505600c8216100c1c0d44103c40d0411030103d209082540c40354125001031a4205060f0b02d0381025404494698001c00480c201900070b40080d040d0410300c01ca0540d00014001700349a0007488940d4a00c01000755201c654440d0344240444000140c450000010140459400130202a45000308251820b800101044e000e40c00601c14400000c91511240c42964158100345c2e1041d40c500010354a044001d0302e911002000c10707001142810640e6000c20008031040d030300c00712600030000a00c00c5400085c030032080c403c0820800c00106195560700c030614180b141c1c0c2074a20301415034840e800c3c180320f4070300c0320380d4801080da084448900d8101c46407407c44107180c00902c80885040d000400f4007602840111200c0040290160959650340c120340c8460b0502c00340d641d10b19101d085402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 348306438 1250 348305188 348305213
    0x20619090b07051e06060105091203091203040503010b060910030c1404090507030f0b1e150c0706201f11031003050c01031104030f02040b030604030c0204050a11030f040503090a03 79
    0x3c00703000428510380c1da194000c90f01c5c921681040c1c44091420344104203002118210180184c403902080c4a14403560350f079851a0762402128800864072242001c0030142141c4100100038400c09081040c480c03d070715009a528989c540c01d003000201428282d505440c80018a014000081c3c00000c02240300e0010f0740c00b45000e00b0b01c3d0f607000c004040c4000380600c211100701d0982c035170114001e11306a102403801002ca060011010f0a0300075900c07100d000c2c40846410556988000d42c00c10380341848020b074810241d0502c072784821400c1d809e00b001c01111f03d03103a604020844108070b400c2100301d00f00044036001440d0034800ca545160362450181c0c00f00d107080c0070a00046440380648400d1044540c441e001d040308a0042008682c81c1a1555440c580038500e000d808036000b9803a80e881d030b82c1d03503517080c400c00c2e01c224043d465000c40081280704010856800030f007e541524138203214580c2000c03040041d2903120700007440e60341417a180c0c1e00300249035008444881c0d500c040e507600d0200402c450485c414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 348307688 1250 348306438 348306463
    0x12030302030906070503240f040903120c2c0d0c0e07080702011505010809100507090e011508070806040f061502070801060e0610090902030a020c100504020619090b0705 74
    0x440ea6601e034074100300c58a120070b4039000c7c1c408070061312103044c0300c02c031411041c103050004081f860f1195506000c81c080c0d400d050000c2e408510314500e013000c019424000c56415000928003e5650300784410100c030b501030510444682c41c405003000c0d8003035443c1d14051412040e042050940c00c03543d580b400792024101207600c0400910b0345400700c3c1d9413900501882c5c903840b050307403480d000700703414500111601c0000a140414612810320f40c140302d803040e481030602541c501c2e500d4800b61801d200000301c3d4100180d01c8000444081c01890010380d5019403001d811001c42d1506c64069200c1000080c094144903800c404d109107450000135101f03850021419482e09680c007900c0405a5403c0c1403401c0b100d0324810b0600400704540020080e1401c00c1c0e110030110038909108103599116480310f8201e0b082102e10382a4268000b40001c40d8030f00c10440d802d0703c04a250000d005514080d40481c0e41405000e070002030741c07122604e080314a175008100d408058040d50580030b03200c4143c3d05160780e40f03031041e0b03000c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 348308938 1250 348307688 348307693
    0x19110c150c1c200c0a0311030d05070201050901030506120706030e0d0309020a0302090405150f180a0c050123070605040b0f15090406060503011b1107030f060b0a120303020309 77
    0x1212841da0340802d85908030103499101c0b540100009241e400c114010041503207001e0480f103003034640d4407040420055405038100d68003103404035003418540400d400e0300700f091000c28080000107070783c00001c4440400b4286804102ca80b100c0700483e60b03018440421202c10700940d040407031220f40c036610141154451000700d40e004100c418060741143c0c110034003c0e4000c4000541400981070914031150401d04c61002c403980b1014610141000784c009882d07181980d603048080c4104001d002c5056450300e41414080c0c800b0885554034201c0d2800d0500c80d8a041c0118246075030034220030400741c00f0505107140102540d900071440c101c001064126011160003a01d000400d02c0701c909012018401c0c41c60800901c1b0a95104041101801d0024070032a181d035124400819541c03401e0140c1c1040c02d500400b2000c00c0980d108002d0f0500c00d803028200a1a800420b007040400c40c001040401c071900f2840c00160308400001060528900d5006070a5a10003000703c1420154954021481007080106 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 348310188 1250 348308938 348308953
    0xb04211401150906030c0905040812040f02030d0503011514090301091a090c22060f031a01060206090d050d0609020a1101060b120a0c0c150204061419110c150c 70
    0x41c00460f9518080900b1b040c054020034802c00950b603101e83e80190043c00440e081100e40011030002c124111021118a0510f83d03062045081c02c00a800101002c1d00b4a68110740c103140d800c030880b5110320880f0b41002850506415041035480c101d9a0122024000380540c280e681846d00d06076441d002d100c00d507003800ca4001404500c02140041154400512000340c081340c10003244051007403d10008202a501c90000600c40441611100254400c0042e10500c0256140c1816050016405807007990400c0b801c0009050001c64105507a03072550410a0300c0d01e0712103030f90100600da141c0008480610015482c07494941100c1d6183d006001c40000307111258903541441d005010307161407503900c0b841e001e01003101c047c481c0d0051026401c02e440d10025501c0140c03181d281d0f0f400407110340c0d010280d00103410301c821640081203c80c0d006401190510b44020502040002c502a00b10202000702c0044c5104084030140480c0c6c800c020020711100044410404a0ba0103911140426446118540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 348311438 1250 348310188 348310199
    0x90a05060a020d180801050a0902040b0405040201141c150f14010504140402070c090b10030608060109020c0f0f031c0504030c080a032c06100b0421140115 68
    0x6044508600706a4060140030300f01a10980d0810700c06100d150120580c0c580c0454401070900c00c49208050701070000c9031312011401800b0495141480e020300030f0341010200030140c3d0b000301542c1e52040400c1415a90b8005180300c0c8440541c851850788031582c2050140c12040c40043d00d000c080c0c0d01c00c052017080159440e41d000341e80044061084d400b003801032008100001110b89204251100a4005454800240d42d4820b07282d005802c42068141d807541181c0c4103041c04150109480702c1030070708100190400c0c500c0caa0354a41403244040c030b16000115054007a0080c85065030f00b00121044503034000107600c1046d02ca40150501c5104c9407506402168056024001d8074050354040c0c0300c41c00c5041c041e40b140540350340030f950241d0500d0b850b2170100291b10001001d045005040c40c11032070b110032481d090385080040103003080169061450080c4621490301045400b100c2000c1c2d40b060f5803c5900303000052504024002074240b102030140241ca048064024400b821102100510403503181e5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 348312688 1250 348311438 348311449
    0x20a0e090d030b1c120306080c0102061602150f011802030f0403030c14220e01050618180702031207020f0c0402180d1401320414030a05090a05 63
    0x1110495055071080c80e103018003900030751200707201c48000b422480f10f400d00c03d14500890b141071282103410900941030010215854420b034005071000740040d10b28400440c3c0002c0d9a08005040d68000440e481d0594036060f00800000c82074038050a42c0031041c2c98030501144042c54240b0841c102d10201c0c4e440c44540c60054070850340700b2004101109041d854688086005000d0303040d0080a00c150344030091140c00c0300c0d1000e450344007200f89802c940d400810460b0003035040d07564817404581000c0c0e40180500e54401066540c1c4001d0882c4000000d1404800a20100448000090031544140900c450b01e680400140740c051a099016001754a50b0f00c0c04aa5a040003000c0038040d400207070030a070661500d500201440f551982c41c0040080803400054100c1a04e117400b00c40303548004140d00d44e030020138050300e04250b00e926445007928000e0480d81d070010019090700c0200081100005003000740728008aa002041070b8210390311780d4558030019140f50f122188880c8518a142c2d000030311460003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 348313938 1250 348312688 348312691
    0x51b070509040803071404120201090503030406020a170f1204060c020f0601060f03060503010c2a02010c08030402060c010f02370f021c0309060b09150f0f120109020a0e 74
    0x80e00d03a411941d2283c039100204c0d08050040010801c09405c0b03441c0e003110b40d1010304068a0f036a4001e851000d42c6100141c00401c10340e01640c041d810520003007040503000305003c02c1c1c1c50f0b0440b0400c03000114490041d0058814240703a82e1610b5404600101c5e082c004021261065114410400c500055800b05aa50345451007000c502640a840180441380c0309252401e1580c4103420082112612800003a00b51813070340110800284080c0400d8070410358980001d00500030485500c1c00702d8003560002040301c841d101e4017400d209000008541151112011030300c080c42110b000f085054005226403000e50701203205c0001d03074480707611031555004142c212540621000b0880c403d07490b52044d4151800704c01908040d044d07005840180380320030b00d480e84000d17201000d55000500040b00e4030b40b5004682e44810300038081d5030080104206503448041034513041008032001110700315418001400d24443c207088941040101c10051440d4005404c01010144211808400c030764a80b080341c3d59a580 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 348315188 1250 348313938 348313949
    0x603050f0f060639011506080c0f070b07031a0103020a020a0b04020d02060a02011b051804050903210103120c050a20040618050709050f0616050d051b07 67
    0x40750740210b01c562510b00010034840301001851501d1002031002060714090300c210603c80b03541c1c200f6420501100070320840300e600c40c40a841031403ca0801900400600c001045144180800250310801420340002d444183d603001101b42042c1c40d10480090107004911001d0f07181c2142565958040e6020b402900d050040c940e000b000c16450a0f200c0d0301010303001400c140c8c0c10001d0100c1c3c010268071040004c080c0140310b0340000c07541344150008a0380e10f80d010600f41c02004002e21940c4441c107000e203010300c01020110f90100703054542e07042160461140640c40d00007410b00c001401c2450500a11807412a40618003a40c0400d12541091b1408640d2210040c40ca40010549000084400c1c1a919105030b14115642648480c107000c1002c0f00c0c9290800030790a50914021003000c02640602d56212400d440c0081c0003500d001e01243d4184a559800c41c41510003203003066060f41c0c1e86003201c21407a0080102c2d01115001403001e022a0b10017130180e0b440401c1c140c0001d00700c40000450008541 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 348316438 1250 348315188 348315211
    0xc0d110a021309020d030503071206050a0b0706140a0606080915010b030c1c0504020306161e03020f0a0c02012a03050307020309090f06030c0d0507152006010603050f 73
    0xd41650030048020700c00000e20011540d5039140c02c0c0961218844c0280e058800d0b1100340c1e0380d05050341c0282080b0ba4110b8800203003400d1050510042d1600382c0c2080c2107401ca50038007034950000740703880005408034070080c2c1e4075a420582044000c10541e0402011200079440c0da00f11615030710911919000360508442c86040810010010286203c008540c08500003d030f450a168428041400a592542c01e22a03490344860038003040d8581400065040f6002d003404140340880010007030414003150800954840484541c42c0907a03000c0e804491a01481c000410740e505c07080360001d003450340e0000341603000600c4004000c440c2e603040513022080070a1003102039698070b406e0b51304541d1a0320003803200c02140000d210360800794075400c00c0e00d8040c0300380308182c856a103440c00906190014103040c0c58401e5421707070100804204045000c000b91400c3e0803000010038101002035407800e140c0040e545a1912107080300c002c4c11404140c0e41c0c16140c2640d0240200c1d00d84200c400d130381074800e47d114072026 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 348317688 1250 348316438 348316453
    0x506090105070206040b0a12060b120402130605091f0e100306020f0f07060603050c0d021305040f0f0b0f010501090605090108041403070b010314060702120d140702030c0d11 76
    0xc0d030241c0098280e40f88018005840c2a841d840c40c42c0b001c0d0007e02d1454045200c507005240300202d80d015200181c10407a02c3c103070818000710040090300d040031f04040e002c0c4e0000107241650741900d41050700a4240a0040c41c03643c00d100405040407405852032132001d8007451000714880104403449030084814001d145072850843d02daa07402907020041030303400070b00e04010a921819501002e40b560301e00030840060580c0c55820305908088461802c14480c008a1120304010f13591581c0c800021050340100041c0e40d5503901e0310300c40b4005103c0c8041c1250082210400400c07800d9000d0038800c602184845d42d850341d8550054030031481c14022040800c41c240500c4046501c20310300c4980c0700703000e000c2d10f801072100d900c0e1090031075010040603164034200b00014020300182401e541c6c203100340d890040c0300740d00d4148002510f03422800c100f5034011000240003080d18020360032410005101c095004c003641000d400c069960703481003038849514000e41400d451a580120445485c000111014041e00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 348318938 1250 348317688 348317707
    0x17070308030c1b1e060106090306020d090204020705030a02010c090303122a0207141c141606030518070e0c310f0e0103080403140a05010c0e18010506 66
    0x296040104940b6a8210500102200c00e810541034200d0202600c041d200c680b591034080d509100456064440d650b0001d00100300d2654042000d500700d0303400c0940180c07246074200c0420060402c850019500034000310b941c2007401408401000e0b40301080d0000c0040e40880c24003610640e1580c48068045002c003296045420802d030000955114000c050140c0c4001c410180c90b1903c0100860400590019070244000800d428254400b10012980d4680c01280400c0d2000e286010010003440000900b0044c000300300c0401017450240380d1102540402ca490302c0c0c004000b004200d500d4040c440300d10000d804486008103035481581c0581d288910300c1c1c4c1c1d0300c000c0c0ad03601e90301c00149071681c0074102e500850800940c41c500050003403140c1414075140d10745010031004107070717039045515200040380040000890302001c41d000c0700e500034103684145220803000c40c05c02d0041480036010f94240040750007a9540003080440b0690116580c10b21b0a8440380205101c200c01d0240340c0e0050000c001c0c0104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 348320188 1250 348318938 348318953
    0x1050c0f0a0c050d09060e01020309060403030c03090e090604030f08130204050615030a0f061502030403150209060a03270f0b1b041211120307020103050a060f120c170703 75
    0x450755410b0801c604004a203030341c0c05242194000706000015080394050005075800a007000c1c400c2c0c0248019404c01c110356000941d02c1c480e5100090070700035060900c9007058020840d0800400400d882c880d002d1030400030054449904a80c12400600020390110180340183ea4050040c071100c3c40e1030032134000550a000c0201005407919a002c10403011f8550114000790046100d0501c2c0700003c80c11180c041d0051b002d692041d006003009409945445032155030000558045070303001801100c050a100107103c000b485044100b41c3c2200d000030710307950100d13010741180d04144088000b21040000c0c201c64400001061100100908103014031113021680c0c0c848455000110407101d840c010081800d078128980c41075010188000038401144240450320a1240e0a54000d0303481e0300718107008520300c54481c45001d80003030605540f480494040001a403040002d0007110300340501154031420035041c503001c9200121040b10002d20302141d01101001039010b0625020028990f0908544d10700c0c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 348321438 1250 348320188 348320197
    0xc0b040213150e01140310051b0708090a0605090609130b0409120f0336080f04140a0302090112080904110712020d02030d0b030c060304210201050c0f 66
    0x780d000140300c0d0100040c0c80c1500c50040c82e40345404501c22940d00e42000d03000d4404050f4005214a040315030300d0203090310040f4601212041203807000601c3d40d6a180030101821104e000c0c2c24020340c4c042048010011000010401d03010301b1202918501e0742d0f42d0f8200c90034440d280c0d81a40259007800340c1c641e90f0a1411460744420b003181808a1000d41000101e01200c80200c1c3c00e4610b100c841005008a58000c03030082600d141d2807a0500816035a100d4814404200304403c4541000c0c0024020b5000a60004040780b10b600c2010155650aa01b1504042e600640101c0203107142c800c500145903e070481a00003180e0780034140310382c5030b0320b0080c43d0359a0f040c01480c01e40c0c080d142000070140990351441065040f00544002a403140b4681c10202c800200000c080341c10356101403101e03440c4a80000c2038443c4085554004600c00c40d4600220341000824042c1d40e401000c04400e210800445140910505011010048154000740401c0342602c105961a201440080241007401c49500c0d0051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 348322688 1250 348321438 348321443
    0x50402070c050607060506100806010c03082d010504270605060a081c0e030a0308011403071a0a11151308090d05010b0909011a060c0111030405030406021005070c0b04 73
    0x2030103000e5850b80440c003668070483c012900c1c540d6401c208495460300441c16040c203600d0749024001407a0400010703044090018024041c0008840050608070701c00e821003cbc266030004070502e900311400705101d18224203000e014440d034140800c465040c4485840c5c06003000959002116408a9444d02e40c003c20001c0c0c19542c101c4111000864014410044042d0508420300740200301c4910800050540000c0f0250a10a810030407843d0701183d071080907107040d10f44241c00c1110072460310002900d044000d500454a03000c0301811902c1c94900314000e01084006502c50030303041d1400c50845615024101c07200c8401542e1000410001e500c004d07000716440c2d02c40c00c0400e19194018001400390f010102080340c0c207030344650a4002c1400d05101454104030400001d004580908540c055200460006280036520209035481d0000e401d401c040e10611900300ea60750f490a06040082d00c0f90b1044c0a07010143c41100c20f0190040c00b9031007858031850040d82d6032068840541c1c0e4010040c400030b40107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 348323938 1250 348322688 348322703
    0x90a0213170601090f0e0a060b220504150e06131104050c0d1a1003150f12200a030816050d0306090605060a020d2003030f0a150f05040207 61
    0x30031086403001400010718003620081001c1d41c50040b0000c151403d81203155042410200d0303000305a0400282070b00001d900020215110751120b011841c222150800010504005942900c125041d94000381c0220301513402c0e0194549000c13001d10079100c2400d0f8000d01035000100088003141d0307084070400014400d2000039038040394140080c0503100d09948489042400003040540580c440c0f01e04100000c8980111024409550025070501904030001c4249501c81480c44032604444041c50050070300801c840b82e0280d02d03050208080c40035182d040303844e00000314100440d103071241aa82d440c000c0c02460000d0b21401c41c0e841410541190b071840f0081464264100c0002e201400341c5c9100345c84603a00010103d10300b96403001510f41651000703000b82410840e00441c241d010a050074600301900703210b040c6d4000250342c0d059182c4c006031b1000c4640000701c180301289a184082c14020b48500e0424480c50015100038103c50141303101c0c0c0209400405010031903070400350040c0c000b09018085 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 348325188 1250 348323938 348323977
    0x21b01020c0118080604060c020613080306040b040e1212130b010b0706140106020606010219080306240a031e2d0f0509012018090408040b0703020c0102010614090a02 73
    0x10041c6071107000e41b0101c2e290340d1a5408810002e0741042207507807094910310401503c074480d885441369031201400d114080c5803105101c0449844681054407641441801c4170360740b240e200640541c54005120700a150301404000c20b14100916120b600c20781d4200c62524000e1b460821000401d50055508842d01500c132800161204e107086200c90080c58203401412151030140002030910142894001713a40070707001c459201080b286010340364041350a40b810000241100c1210828402c0c0c11a640c500e544001015030740c40f40d06030040710b803082c07030060101c0c400c0404e00501c0c8141c540081180300c0f110380e50b40c07a0004c52058424510050b00b080306000586100362a006415142d08565940c1070343c0d101c914404100c03031304c1c100314640c020000d1601420041c1d0100d4a001104144410500c42e0007440080b0741800203402c101c0340202405200745075640c529240207900c034801043e040d8090351038038000007950700d200314a1106028004024110340e0744e8010724100290015010002180b80344d45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 348326438 1250 348325188 348325199
    0x80301060c0204141e070c08040e060f060c03040504060e0106020d0e042903070f0b03070f09180e010e0f0a0303091a0117010e0c0f04180602040f06021b01020c0118 72
    0xc401d40c05070b05910004042440e4400c8155800c000282600c810002e00c0000c90010235083e03019202561080d50300f00400d074a13950006441410040701a591044001504010000d4004010b10440e0410741e0300b40012a65a007190f40064024880c5401503048440b00b01c2c6e456105034491600b0100060000030f40e80c2e110b1100030300800e8010744000000e0228030341001c5520302000070800410001450b81005030404034074000c5404080d0850341807010b040c0101080d203004049100103009801540d11212191007048409041d004041d08819441d01180c45080310020400d50010788940c030003025403120980c5c0c00c8004242c5600c043d00c1d10225000700300c09954608403a0b5008054030b145078501d580107403031440d003110000c000e507102550042200011689035101c1c041a40034089900050040c072904888180d20311000008101c90b200050110b001e049800f4050140c52040d42100c40c55118804522270012801c070311940581d100c480d04211a40c86000e52070600710043c04440f000c0f507580c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 348327688 1250 348326438 348326471
    0x21e03090304030b0604090314030703020705101a0a03050d14040b03010e04140f0a060504031b06150b040302130e030d110702010f051c0203060d081c110304080301060c0204 76
    0x64540e09000e8000181c10000d22100801030380c3c201508841c01c00c041806568080c1c07800d510b501d480c407a20310010000a11460099058549d0660020195044505072070601c4009017140300307140c44200c4810456401d0f50800160280036298410300420407141200001d445406062084241c5110200b10228004202d240603500030f00e81c003028aa61400d141c41e020850804c000450900c55002e420304808000c000224801580d400c170000041588550800b00d4030070501c22100a00c0003200d0b481c5000700b04c45076000301820801d4081d8000304035200d00700080c6130b21035480040d41c071000702d100580c202115644140c8401c2000c07000c0740c5c54400560b800f42d05561446100c828840ca000c6442d4080d96001010350800c1050f81c03030884e00c1d05c000c0742841e00c1d916102c8910a0519035000c1300080340f503140d06048400083d0071081003900c5403140d00701c4c60181c414100c502d03524582072590707a03607120080d003082e81e000d40d9100ca00181503030708003807080750b204601c8503060341d20540b01d03007649801d200784 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 348328938 1250 348327688 348327691
    0x201020a0807050c0307020d06200a0519030216053304060e01060807061e080609240a03051c030504020319060b0d0605040b01051e041505040606020304090605030d12021e03 76
    0x65a000c640d0503042c4100c0505d24400d03000e03000310342c80b0400081402590220880c3c140c02101400452100740303c2e1411030090140b0100580c0296415001c0400d0040000b092c260000464181e0090400c0303011440d01c50341820307845108102d10340320114000400e590040004102144000501d440e543e0340610701c0c207184c2d9031000e8042401504202d41004c1601614001c00000c0e04004419090800205496050042c00e00100b2140f0314801e10703d00484000c41005080700130f1210f016543c0340e0070801d03107511001460100040241d85000c0c402802806020711a64006020300000721403541d81e1140340d6010b0302c0444001e03544d00000b104d02e949180d811021240215000a62844c1c5481e010380e050f0010f03007145108610f6452003001b850700c070340c0d040c04440e002610301081c00e4401c40d0826502d41825001164882e007006070100e0302907400000342044900b001004c1c00a03030381e581c0526840c0c2c111540c01c0f00c0010704d5070502020200440e00102a40d281e0a4515003e06102d0398070310415810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 348330188 1250 348328938 348328943
    0x10180b0a3308010b0f0d0f0501110a02060604090309120c09020d09020103051302131a060f0a080c0a05030c2d04060207060311070b0915010f150201020a0807050c0307020d 75
    0x1080d552841c8880c4092180c180a042d00d60300070000c80055000040540001c071041c0c41c41707106452201810004100402c920060740913009204010301c041802c16681c00a0310180c0040c440c0c403001406074602809042c1481d80c06449a60b000f0b82002007a03604814515002d6500c0308035108001a2200140300400d40210302100008010707038148001000e0b90f80c007074008440381107900c20400c0503a85070002d200135812030f20000108000000034640d0500031845800781e00603004181c1180c860400d1000341500c0f503465403040740d0366036011411040340c02486603c100081060000410001081c4000c04ca00e90700407004e10450320041c66040b0151800c10700c2c184100101140402c15550100451009400f95013000d1240c14030a0919a0080c000c500b0090a1014590080740e003a0748140114900d103070800720a940a0743e15884201c1d03060190748a03a4500c1c90001ea50442c010788180700b510412400c41c3c2c0c4030130840c0c64085c8229600d401407200f901e45800200708500069039000350941010740f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 348331438 1250 348330188 348330251
    0x7080a110a052406030718150e060f01090815060f03060412030b0f0618010311030a02030709060e010503180c030102070615050f0a03060507090e0106020c0310180b0a 73
    0x209070b100b0b83e00c0d059405030b0440d2900a16075090200756980843c1c003805550481c0c209900c0c0005440b00e2101402d65210080c0025000b0b081c04581404203200440c4140429075030201c4140c55030004446414003482501000e81109a40030302c042000003945401c204010220b600040d0600c0c00a418154150390490303400f0105c10325511100e82502505210440c02c954400004070785401044542c843c00002054800b107250101e034140e0b0007035101002900341d5404458584c81d000b041e005c02035000f50340c80404540c1c07200000481612517010101e480e1010fa580f2030550302c8543e1540040c10600606143c54011200241e0701c81d00c00344081c00807a8080d40021509640089012410828a030400c5000301c0301c00548403000e480700301d800811a0b41c4260001a5039440510407110b8841940003401c20742c04600000855507800100e8641000c0100c3c1a0740141591807440e40c200d410840c13a2019000380d160b030103800324461283c0150320440188001c50300007203490f49003c1d80c404104803950388a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 348332688 1250 348331438 348331453
    0x605030c040f1d09060106120905070b0c0f07050a061706010c0501020a03020703090e010b070b13020a090608150103020a0603020703050f0307030e06070c0b220b070e040f05040807080a110a05 84
    0x10101030350540e400c42004c0021340529410948018100103280e8000140180c0f91041c41d4100442000440e008007007d281c10f94a076211500e402d038481e501ca020440703551003044c9000c183c500d4042c83e02c1040710481d441e0308400c03400401d00b41c4e107240001885541444040b49020000c11000c0c0014028000140e41c0140c1c0d9041a107009040529580c0048401543e190018414040e0590854541680200e082913050740c17000d46621102d02c60b040000c1d0841880c84000070a00d0a640010b4181e400200648104880880801e14010000d02c40a54000070345801000302c5402a4000c0c048030f4000c2c50f00c146040d880d101e40d07800c030342e005031010700000390344614150315400248032507a0010003d1601c1100741034241c0f10080306440140ca612400c0101c2010318100719140400d0822480d80600c0c403046d60301d4808006401740b11105403582c0102d04004c0c903c440041144610344c45250300c0140581004819201d06601d0742107241103c01741700c8030305010352000400700903201e81644141c000f070800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 348333938 1250 348332688 348332729
    0x20c090a020c070611011b031e020322023105010506070309150201060f030c080601080a030504140609130b090106050922270302010f23040804181505010215010605030c040f 76
    0x490510714809c8014600c1881406061410b0f8003042d1020407882d050901c001c00e5500001ea80c001200d01d1108008c1c925200d80c1c0c440c0d0001e0507603102c004e081c1c09020002c2c0e0381d959040c40550700c100e1800030b0000c0d0103c070040c000c10a04580004400c1300c0c92000040c810741303480c0d0f007444a180580003524990711001041000034020800140580000d0b03000d800342d6512954094150b0103030340201202c1030811080550303507071101000c1d21420440100281036540b60700300904024401141d10300e0081804c2c10021038803d0090046807001c013400f401440341e00801451414109114000e09164a5150380b0040d00e1084092141900106d44500c0c00f00003003514070b03001c3d085030441d0300c803001c1c3c440c186400d65011003c3c0c00e036080307640c599408550382c8650300d524000c000b92145030080c8201d03046901c1c0800070b002165001c100183da114004004c10341d140c20040ea40c5000c2c143c42c1d10410765a11005101c00c07849440919044412140d1b170307a0030030b9181c014070000017a4a4001030074044103038035030310304 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 348335188 1250 348333938 348333971
    0xe01090f060c050906040909020d020904140f0303100e0c07020303070804081005010b19030b061305010801170c060f0403061407080a0e0303060d0f12020c090a020c070611011b03 78
    0x1201c4607050983c039020001300440e55034000ea102d5007041960b03072a0b0354000e5441701383d80c40c1e103030650050000e8210300e8186080c0c40d0344020000240c14034481c0517124070310041c0000440e070080d00c030640c0c040111031425600c051601e00003045e01c20344d4041800780b0001070b2410000b034a0141d02c940d072010f48660401030100e00e00080d040710140218148001008603c19940483e541f1004203608075100250f001000d41c003512114901c0f070f400c12800034188044103d0b1000700c00a8a03000d0380d9182c201c4e41e980c1c9110386004109004c8541640044110300780314074051000b051f1810031014000c3c14a41d0ba61614001c0340c554420540c90411054100700605a2051081d54070901100080054101703445a56540e13000080a0b140038681ca020103000307004d507a004606160340d00c2401d0155030300c11a03100079182c00b02291071a0280034500d0203d0f25140c900d009460359003071014007c10300b00d03103061012508400000c01d54007681d548c0e14401d652803900d08480c891165519140450718500c100c0c00140d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 348336438 1250 348335188 348335201
    0x903140304060c111c0602031911250803010b120c0705100b0402070804080a02011e080c030a02071416051e0d0515180706091d07030e01090f06 63
    0x11550030800060280700e4204807030300c9071039400c100090030b4a0a0880810f4564501404030710301003043d55000340400219400a611428140700c840c6c26254210014505848000c840b400b8504418440110070502491105945400c2e241200d40c0c992025110380005078001e803c5880848030000310440030710f0300d0703441040e00700f81104a118a0001c2940710962190400700040600d40e407104491441950b0306e4054070503103504440034550725595403c84c2543c8200e040422400301d040848084920601c901d918600c3c00c6243d1950300709a40c400743c84090320351008004a1581d5800c0c17180101090b00004210422010701c00207240041c02e588401741c4c5011141d2140740300e103810f40304000342449000c00c1c2003022501036503a50891002490140c1c1403106a00c0701020003c01c900c104040605003003e400c00d1034060344140c5510340e8071240121982141c0d03000d0030304500440c40e00400c24044c07010041e5030161040c0740005000300101c1c5010300352200038a05032180f40c0f8040c5400c3c2031040c1481440c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 348337688 1250 348336438 348336473
    0x509070e150f060403150b0301150603090b0c0906041419060201050618070909050c04080105040f060e010c0912020406090e0d090b0a08060d05030c0102070c230f0409020a12030903 79
    0x5080c9807039640c0302d603136646081d0160041b483d16a002c0010079142500688010080d1040800c8056160b0a00800600940d00161450340542001c1080d050440f070454005a80c0a00624a002d00b00803000d45130f03e484400c125003004080b42007a040048075021000076021550000c1100e003412810084a000745c1200300c01d0154508052000060704844000d04450100704041056500e030350704036055018991104081e542880c04000c10801004000145280304080421070041e900e24010700702c03001d00c40c00c1404076403a1031052088000344034440c0c0ca180d10050021565a498402c140c4c160307201004c4030500d503801003250134001500f00300b140300075241c08030400b4200300002c0c6009100a1014144601030070358042d01c0c1c400d00000b03204a50303c03210700c403000759541c5026180c91842d4044610810298412202d1012140748034941e80240700c00c1c0080c40c20f111919107208001c020030391800708982c041500c00c1300048400d40c0004401d4036070b02036142c84188610314203001c500700c04010500f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 348338938 1250 348337688 348337699
    0x4050d062a0516051603060b1e0906060d0b03010e06011a090916091e0311010201020a0e1201090203011b091203210e2b02120403060509070e150f 64
    0x242601164010705446030f0243c2c52000050900c054141503007003480f4400c0e20f03d500c05013842c2c08401c7c4a07086c0c000f180480d405403002e14261110035104000001d032000d006610080400101d070042c0b0300300d00030701107100f010080041d2074200c1270002404c5035a00349411055030402c0c00101715854108041601c3d8100800480b0b01d4400b04600045107050018900707010300804907004041e0a11505d100405802c000c441d000c03496505540d5884240e001d44801c46000d5000d82c1d413001a544103000380d410482440c1c607042d161036100000c102c03901c42c0c01040710041c0d42d6501c003090b026a409000e000020384c804070002d8414003010200034512050b030b42148440300354008078080042c4d40310441e00c5400c03424100b0085042d440403070601c0541402800c1e040c1d244100c00c2d099142100302405001f4828400d600d40005100c1e54006a80b940048a14410912800e000400100c0c081c3d801450303120815109480042e074403211501d000400982e120650424001104c1d0024108081d243c696440111034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 348340188 1250 348338938 348339011
    0x13020a0e01231e0910020a0209180c0f01020f01140406051003020603280608030a080907080304180f0501120b07030603150b0109080f010e2a090c04050d06 68
    0x1502c0d8124403a40a01c1d03180c590110445100150038141600c042000042c040c1c0f00040d150000255113111064003a031207400e100740072401d18950b41d8482c1e03914046c003e003c1d02c0f41d40005410041d08034007407141541980035810321050441e00a10900e002041e0501d08009281018200542100c100510f415018070a07000288007503903445041c0c9501c1031a030130005d11002ea80070394049d84003c0c4400c11b1301394607040031404101c049010010780451520b50355a6a1070b40e4464108030307550105c80c03040da140780e0002c000034003c0e0f00480710b080416400b05400452440d4090000008541c030907444600c082c02c4250031101001514070741a50088154507081c0b00c6141992100500c622901c0e1540390050740d01c50b221505640a10480e50040020906461075020281a0030340a0150700303584da111400b4040c18100011500722040241c01e2090800f12108107107c4140604c22401800d4070f90402c0c0144000141a030b12900241d00c55440f03100701048801090b070740070149400c44010540310701c82100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 348341438 1250 348340188 348340247
    0x109021201051c060908030103030f020705091503030f030112050d0203040812090f030d1809090c050103050711030409020a0e010c11190803070818010801030c09050613020a0e01 78
    0xe080354150303401141d120b1400d0340068255450503c040303000a09403802e12004c84103205c80d84010394100d80c081d846541c40c94690716000c130f8441543d402002e0303111840101044070800340f004451700310b40014003240d01c1c10704880a01032498100340e00c40c440881c00c108845c81049810b00a19075410000e000460905044c5280315858007114070b0080d595107004aa41200c1c0c0d0f440406c1d0b00c900d0f4801606039078200d401d0250003418061440c00c15604019200d0002501090a10134806201d030030040304003442c0e09007001100a048080c080e44108250f00805031001c45041c001800108820180140c1c0c0b0a02c11001800b10350205401d24180004606040d0114401c1881445078000450790540d5462005410b01c044222541001d0128800400e0140030880d03e08000d1142003d042191220511001c0045415540901000303003c101c000404000d580640c0c0c00440d0030120050400d101d01003440b81d600c00b240c01c01c2400b40005856031281880558110181c1f10380e000d140000d4480307040251 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 348342688 1250 348341438 348341467
    0x40f270e010b060c010e0706080c0d050402010e04020c060a110403030c020f1f180605030105060304060c0908030a0801051201200a090509041209050a0b0f090f04060807090b0303070f0212070801051905010902 91
    0x1519450744403510cd000290440e803081b4a00c50710000010011915207000340100760780c0d0042100c0400380c0901d4a0060513850003c4801d4400300c0b03600d03a03030302c0c040242164207100c086c050034050281c008410044454180c62101801040900c3c0e50b90b51100101100745040d00c682c2c83c9522541c24800c00308014840d80c1c0380c4000f280d6005070000c1d80410b5200c28514101c0300c5401d2648039140d58000403450040443d40030804604942084034202e0656032803030411400c8502244000c2d80a2820310200c0404000090280c205820b00e1300f13224010170350f180089515510115012501849400a111610340c4c014055a021382010349001c1340c85030800d03064810a1003045810100740c440420540549c0d5141380003c1304412020b8000c1c083d0565400000740c2e1428140134040c00903007442c41c07110080c1000010b980c1050b810129800500f410394083c000319803e040110001401844030102c2e8000c3d09014a0380550850440e4082502800b1009821203806070012107202c6d004000d80c2082c034464 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 348343938 1250 348342688 348342697
    0xc060b0603040b061c05070f090e07150c050c0409030e010219230c030106081f02031005062a2116060519060803040f270e010b060c010e0706080c 64
    0x1d449140750f202402d505c8450010300d100c0300414600c01d410b00481c4070001113001c14102c4030f4000c8144410b4000c07600c140e0715403a40d40111070490000000d0074441500c07956003240000e0050050725500d61650b0b0110f0241d032481001980401d41e8281c240c400d550381048410280180040f60050b110750300d035a5444241100540c415035030000e0066100e60f02020b100560810400070000c01880b41d0714010542c44880361804103480541d416150a1010500c4c001c0300c0c8103103e80d04091100908010410a13540c001511201d58502c42c4140d00341364800035040e0170f2002410b600240700d440792000c40d81740414a01180244108000d00007040703441c1600b1048d82c1c0b6180d01110102d15541c60b0750101031038944110802806d41c1c20002d000601841c080000e0007030f20001520410b00d541c844011540d82c0e899101420000300c226848184202c0382c40d44010744000e49480041130104c100d000041d0241c0040310f510a503a50340c0d12a480302e403541000048010300c120306000c81180b5000f04001081d014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 348345188 1250 348343938 348343951
    0xc1f0b09011505040f080d11030f0412080403021c050d090b0706020a11060103060e0601090c1b170705010617010c050307080613020301060806010e010518041a100c060b0603040b 78
    0x1d07001c2d80051240c0c0910184d0b40907200d0700c1000d445141e40d49103c10794400d00ea09140d03020450280103890050b030080216039003c00f041100300e141529000089040c1104035406a6601209110100040c2e50341006010b1019401800d48280601030500a00340087c0000420a000412104014004036801a510200e4011400580340c1d64002d03815920340300c04860398039480c040c80340044100415035202c8481200d0301d000710b402c141c2c0c80b03184003c00c55243c0c880810215070f03000101501c0245c4044102646803182e001d425149461102c802d40300e0f0082e910844031a51982c00500c40d4550544075422164191402801201e0f0f401030068014072018019074100500e0b40300040d2951a0b181405070442840c44c000c5540b581d450b40002c08a80040d13556500042c0f061032400f48070741c40390060b90000f400e000b450b000b0a800a204010081c40140f1215900070300075036000c10559503540080307084c2c00003134440440c200098500b81c41165080c61440d4401d8000340213000c04140c08486842e0f1015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 348346438 1250 348345188 348345209
    0xf150c020a0306020a0519030c08060d031101020f1c020304020a03080307020106033819021605010c031517060105120313030c0f170607081b0c1f0b0901 67
    0xa209001040e200891908060710460001424801c0c090f441401485041c000d400c501200c191802e200301c06a03403d02583d08001500794000c900701340b50140d078a044440c480d0801d600803609100d520707030aa80041d1100c03143c031480400e031880d0745c03a203040c03014040d0510403000310316618065000600a0f8214000640081d401000254a83d8004d5101d280903581014032903015a00408000c1e80704140c9070440381203d403402c150461042021f1220034011105d0801c01c0c00c2c00319030047d0040094101461003810b0000380c2a401c0c000c02e40a1003a450609100d9501203150b06841602c415020401d0b0301400d440c000b83c112240c40c1d85800b21b06c0c2d44c103561702110040398502d0011075461550107042800800340c0305811000007040281c80f2900b040303072010150100025034409a915025408200c0417030b0031307040b410005401030310403140c0315800454012061007580d40ca4005c2c20361a0000e0000d210f00da486220f0411107000031101130201710490f080c0903c42c940100011528920042c4180e03030142 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 348347688 1250 348346438 348346457
    0x61d100e0a0311030f040320010f020c1c0f0c08070503030a0509091512060403020d02010e0c12150106050a1d1008060402040b1303021219290a020901090f15 69
    0x40070240125080b031950104d100751030b1a12410030002310a4101c2c800380d42c240741d00142c01074550069042c0f06040c04c44d40c02510240c13011005100740c0b0b000854a1240e80d40d0481d612000050590b8502c0c2e40b45030051030ac0c280c1081c06d03d038000d46003000e95005280319600038003180e800e059104045075059a002c0e11800540e44410025015409007502c2e01a0300440403a501d18104c40c001074214840c502907400c0703a0404082d908103908032000d60611000f1a000700e503500146040c600700d60422b00c0300000444102c035158402140b0f5820017038100f240020780c00207004010790742c0103380c520403400e05403a00c0c400c0b9404034000f0314803407a20720b24801030101003400950785075581d9040d90003c1c88207181c010783c3c80002c2064207030301c140c0e2400100e01c520352540c0540b008010004564400004207003440107548501e407165043c01c2c0d201e2501d4000c1181400c1c90905c50340d451580325011700a104000b503120440000050040311280d00036501401c005401007040311200b40b81200e0a950605008050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 348348938 1250 348347688 348347717
    0x10b150a02071701150b030c040909050c280506090901060e0409080a17010b030f0103030c0615030606030308060102010507050406030e03040305060412080112080d0216061d100e0a03 80
    0x349010b030b038064910661400c455412420064020290703800d846021001241c2c0c1721040a04540010703140340f542d100040c042407028060f41d510800300305001d0b20032651001e10307035000221045001c031325024548900c1d03403cdc05030041005030500007426003110700500b0280601c000c80d50000d8144501003c2103507501c0e42c440d0a4803541d210050703079078000c6060750381d81a00b143c010f056030301110781c4980c0030184000006004900501924003c4d060b07404520705603440c645045903a12485207007560380c1a43c84006000e6814005800c4000790b2185d000855894914100030700710660040009041da4105802c2040750742c1c0c030800300c41c156407003820002501c68803645d145141d4000c3d500300408500c100d0080c04184280c000d000d14800c1070030741e40d0710030396a03e41c4030924a02900c850010b140e000180002c01c2c24542580217020225280b25807000805102c0d00da4000381d60a200d07a0310490710402c0f00c2d414601e0002d001d8010b10301b01d841810b0007104c0c0c0e010350643e500c0f40d007181c000d02000140d0181d03648c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 348350188 1250 348348938 348348943
    0x3040506070b0a2c0c030115050d030212130312030b0306161808031b0d05072306190f2702040908040b030a0f110a08370509010b150a02 60
    0xc4c1d501841c01365001406440b0009602400d6099100e50305100e0410081d03802c4c40c0501484130b2191114070001c04c254035040c140704061661400803015401410810b4204118000c040c119065a802000203401d140d420314415100225102d60105400e00801d01c07203e80f00016100d801000a000400400503200c90440d10034001e04900c8981c0500380c400003030f5256000015100501c98a0040002c81032030b105017540c2e6010081e242c00219905008040203e26900d0986000141050340f2150995140b400c039414080100d4005140c404503102c0c408030164584951007244005070410090955140500e80181c030404510725032026903448800119101e6070400c6800c140d0003428662176a88420405046420850310081020b24040303061004005d117004080311a1a510306841c50040040c1c0200c40c0b0081c01407840e242d08401180c034028503a83c460900840241c42402c02138640d034a1100e400c15a14027a00702801d60303040070f801c46c17200d5407151034104602da1a640c6036651544100f43c10b0b070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 348351438 1250 348350188 348350201
    0x109091a060310020f03010503150618250201050708450102031008160e07030c02011b02010b01090b03090304122117102105070e070504051203040506070b0a 69
    0x8106900101e802c0b1301d613032021000b03113069480c1181070701c034400c08807000c0490340001101d078039600c4040c24920310a000743318155107130801048208400a08036110031040011a0801c101006039500ca04024400b41e00c42a0b0b160880c1a20070074108000b0484401403010744071901880d0000707020f610042d0b10401441030001d400075100025900c4c0c0c50041032201410080f03100306807071401500c0c000841860040210400d032284020308080f1511401c400314010540030071008213541d43c54030400b4801402482150071240315a0022996020440005000740041e6000120000d0b080c801c1c8015150088244c80684111b03010044024041d0700300703c4c4c00c0018402040d2606218002044007250781b10b004c02c294000c1e00541e81081d0f865008440c12421038901c10030541503010b250211919943d081000c444502842c119012591145184840e1003015a44800401c100060800c01801e02200e0700c43c0016200010754205803814021401e0f511506c10001c00402c40800054005622a803001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 348352688 1250 348351438 348351463
    0x3021003020c030403140303070909020c03120c120103050d14090609101e02010c030506030a0f03081e0f071b050c04090c03050102031303020c0406050d080c010209060d140109091a0603 81
    0x45040c80409003007e8682d44151004400140000d0700868442442d000f103803040703807603030008601c3c0c540181c520403421230000d442d0010718581000082c29468450b940b907406180a0000742829450010016140881d41a081103485000744092803a5030b80d10010b45016030400d4450040855085100322440010402c1003600c2c14032210000c58081d90540c03200ca00910301c0d0b1002c2103030361a031000301a92580400402050404c1d001d10761000079100c0c89655401901c5800d8030994110408401259510200e40140c00d101b00b5008201c8202e81c0000110b2000309080c002c14a141d0064403029110030510001500403521407803070b1000c03c032900c4051802160050700864803410140d00c0184030540300c0a0903801071144800c4040c06290910402044681c014440454040345543e442c0d12a08800c500c5140d656081c81004120380310030000f004c0e0403070480700000c1c1c610a84410801c0303c40e41030300035119183c6031035504400500c140385055103a8444e00140702040e9a240300103454080241a407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 348353938 1250 348352688 348352703
    0x408180a030b0108011104050303071202030d060e04020f10050318150a150e060a03060b04090506072006010f0303180f090b030c040c0203030f0403110d1d090103021003020c030403 79
    0x24001404940d906980704d1400070701a4280903074848946000310302400307078190020460207002074280310000245455078016a0308110101c090801211040c0e4000c00203880e044040008501c1c00040d2007420304012a40d04000310000f06000b0594000240070032012581c1c1041201e03030100c00c0084404484450f0308181181c50060540c0c401740002c201441c2505a9912010807003242a40c8002c0c46014058100005140b0310784540010300714074a000358010340e8a04554001c034005000042c40703024591246800140c80c52968946100941600304c442d4010100500c003035010b42481c1c10480c0d406180c01d00c0c1129841c01a4809050740b41d01001006103680c80010704415550880c1030401c10071001d58001040000902c07065034860700804005820401c00216400003012000350404e009242c005600300400a0141c5031880a03030350000402d4038400725010744411026a83d0b0400810b89000c41103501d1940801c1000702c1101c61340c800d240d00802e8041140c0f1040080e1001190091b80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 348355188 1250 348353938 348353959
    0x709030b130c1d0601020c09220b07031b02030408070b07020105130801061406130e0415020f180d0c06031113150219080304060c0e0d1505090f06040818 67
    0x8401d50310000f1000210300c11038010019031158000b08481010600180c5044060350b40c549414030141162072114010020303a50980c0302040132480090b108094603200050000d408645a100c195502110031013103602c20131050000000100355a0111100b003503415444010034401030b10300f40241e03080d50701a800c4201c00040c1da06015000f0340d00300c80c4070b40e55009800b80444180412072284880518002a0702c48041010100e0800300b15881030180a1601101075220340701c81c00d99020280e800c2c40320347c0204482616090035411001c0c000d000300c403103c084201503510801082c46d68400d00041c160f42c0d003103c103520081d2a08591440020440002085458140054401c4c0111280d02e0042c440c4c0c0000040d81d412012514502c5a0003001c41030541d91a44e68880140020301080010000f0203518048603855404071496644e00c031f881000501c0081e0071b9000102d44d0010500a29039200d14004c6c00e031200f02146860b04141c0109402d60340d000303500074081040d41602201604412280c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 348356438 1250 348355188 348355199
    0x804090b0d0b0403030b0a05120309130908210f09190804080f1609060e01170102070204020301170d14093003041406030c040e06010c020a14090c030709030b130c 71
    0x14808143c0310b404071413507500b00d921003027030103c100002400c1140940c802c102603502850203a02a40c5403480502003c100c3c0070141c1c0c0c0380c460f20741000700d18900614904222104002109e82c05661006044180381003a1070012812559020581e8088a80303503410b035503130410701c080c4600b1100606010400c546000958420305e580c2c032001c00540c00d03841010b0400124031140c05002d4030382101d072a40d9500b01c0a900340400c500040004e6000e4916540d403c115283c01a100c0d070000c4d5000b0410300c1e90103490314000e01022404d181d0540b04c4e10f02002800384110419456500a46842810550300306c205806604000c0c240f60014039040552204503260910030b2500001c018400d8a104240910100754000c0500c8110b0006895803440c00d1030600c4113100a03a0542c000a501c020145000080b001e0207030013103091b044140d000b40242028091503c00d40d810712074099508a260802070ba0b15629094000512090260000422030104035011414280345155880003054002c1c0c0300c040459030f03d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 348357688 1250 348356438 348356441
    0x180209090a110f0102250905182e150b070501050405070807030c030f060f060801020915070818180c030a0501061b030513080a0f020108060603040804090b0d0b040303 73
    0x1400c5401c4880c8104036940c50415060201da43c24068000b04010352170310702024040ba0300b089403c100010fa0100014000b035890103454010240c1136502c110080c0003804d01030500366180303a4904856120034140512250b140b0310004030f640410380000b6424036149102c12a1061a484042640c0010071150107200d4194401d500079446041110300c2c3c9955207001940715074840c80041c00e007100202c01000490000e2100e5a0401e1083d08000b43da1007810240004a400b6504100200ea50104030386005080c46080481c02d07244040041e41084032590f90a84548200071545a04500c60180c50703010385c03100c114604a410418103086003078603150107000110f81046400309002c41c00c2c900001540340c00340f40c540700b10401c559070030b0401c0760840e2070a4540e030b802240140f0408060140000300b085062090203a46c03880b92000482010f65030000400c002c1018101612450007001407100052042088034211041003002007145448880003a64083d00d10701d0140102114104210406506 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 348358938 1250 348357688 348357703
    0x30b0a020d0e070f0e04020607020d03120606031401050d03031415100815040b0a0b04030305040e0106050337020705060a1a0d140319080106021015030618020909 71
    0x21081d040000d442c815002641d1580280b0418400003403800d01440f1034010300825950150024003114508411540840d4034403a49040c10740000d408030421602c0200e880c0180c80003402c00b86000c1c00301211110000c4408030040c0300d4280704603462800c4904160082c0c11440d10f81f292039043c860540340c00d00700040300c0b444512050344a040c7e0341151710000790280c400103014103d4001042c0103a04518103000c02843c100d0355043c0e00c030109100c0020380124400080024621a650300b40d1100d24102a107060208180c000800f4003006104111609004400c0c1544013540b800c090903400782084428a14500304080040085000103246000d10400050b43c60061904d11020020b030341280180c00300c510480c59480c0d0b40180040e8040d0086155000d4000d42000c2240c1564540b101920444c6841195404840f010480c0d217401000500d070144203c0d402d40894181c14459600e45085250501c115400020141565450110051b091494540c209a9400740c03411195043c0702d05c140b0f503100358 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 348360188 1250 348358938 348358957
    0x303091b010f080a05040f080a030c021605060a0c1b0b12070f052b0f0506100801080601032013020319180320100b0f180c09030106030b0a02 62
    0x240c0d011510035442002e41c1104034071140d46005441c2c03103458800e00174000182094403001d0101c2c0d441c20120b03105900a005605040c0c40001d1095008007010f400d0141400c00d84042d43c0c40c2034800c0205403291400c072030754a0194502410405000e140050004200c00c0d1114004448a24042030704102c45000700629001c042c0d40300800e80d6190700454680015420080000f407060100c280903020309801042c07d0111050986d003040c200400003c1251a0031040c41609901c81061100d50b040600b41040c48290a1901003503541c180700e1090f40d1aa0103200041150418034002c1128100c200403034003560030f004203803e0072072260460040c0030f5003007640c40c1080800c00440c40940b05030380d4841c141020541c048094841c03801c0340c60544804005840000704280c00009180780908244518503608100307980005c0e8040d210814401c40d000d404c580b00d401005107003088101451829111a440f100d1080240d80e15190800440d01414980d031000b400c40c5403203c02c0c440d8061094028043e25034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 348361438 1250 348360188 348360223
    0x20f090118150e150313030e3607091a18060d061404061404020a03060f1d0601030c0c11010203041a0301210b010614040b07060b09090d02150a0e030309 67
    0x1c0c01d140094107a00c8190b800112416406c000710000900600c044a100c8200030850321007102c265011801e080c600b06040c1051410ba0069400354071003190002c0e802c182e6910b84032001038100524000d10452000c00510400c02c08210079201c45082507400002c0d0101030110758580c0b0101210001400c513038000c0c003210b02c401540380c4110b030405120b001c3c2101c0c3c2c100413801d1280c2202c4280f1009501c850041d0080680b1514042031150071084c4400c0103084c03a4510280210801c5c0c891411030320080c0c4814105030a001c44042026480300346159181d412000c400f00460104c00141c1c61840b9a030310580f000c1c001c0f0003101c24040d644001440c1207605e84114544c1c02241d41808202900394013400900c2606100e0060140b140b003110280b000050603124075141c1500d40c6201c07441e580208208880a907120303855882281000d800c8543c008241c0401030000071481140a500d446040030900b65207804280000c6a481d0180c0200805080342000c2d607541c0c0c180109410748514180b100941e802 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 348362688 1250 348361438 348361459
    0x902041d030703030f060e1602070b1216090e1003020414090703080a1809020903011409100c051917090f07090c05070501060b0913020f090118150e 65
    0x20046038019041030080e00c0c0954640490750380c040d0024209504080c80d2580d03114008070700e100306503000354001c480c001c0f102000001c5c21740e0000d207007d840c0d8104d103501040038411040301622407141281c1200741103146030320040b203503181242c1507a426403740039000350880a10440c07060307500d8980c1c01d07a4020390b414010041c4502541624200503140300899030711448c4100013084c2c141000e050500d019240000003842c104825104801c515004030310110703800201c0d64a280780c01d209180d10075581580c903805519144109549840b05d0104588400c6d44910b950208148190215a00901c00394000c428000a80000070400c0005a11004800e600040442ca468600080d0403000000d090000c000c4c29080045a1001e0302202c64084107111f0b00b07004c6640021400e0080101a0441c1c400080d2034007103039801c0002d40420b4160010000d8810854010052440d00459203000c0702801c20071400180d80119200c22080c030b034800300e054a1050705400203141e00004850090004a402d8082c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 348363938 1250 348362688 348362711
    0x504080d0806031518030a02061e2a0d050a0c03061e27092004061406160c0906030201140306100c03180602010501031202070e0a111606090204 63
    0xa4107402d403802a490350104191a0905609034601c1d544100000802e406600b01084032514607044210100c0146c1c000b202003081c0c454541f10700c40001c2c00b4440c1d10380c0741070500c0b03001220a202040710740c03180000c9407070301607050f9020081107410700b11203a1010480c0b03252010011004144030f10001000030f09024000684070b41911940390100180c035411140e4a00e007410001e126529a54407040c0403810500d0034100c1c035039a10600d00014021140c4001d462400c1044070906060000c001f40b00e2460b20030207000c00903100700d00703104601c01603452a684107100d0145440032044000010101600b058010441403099000201124404c0c0c8900c08518509900240e00d0302080b1544d42d0040d150410392920707140304041b610420360207400d001d4884030380f070441242c0f42c14094100c41d000d80e440f50010010024610314841889015102400d5070600700540407207130302c8011b03100083e25078948c07a40042030104e07401202e01c158540c0c000b02015103190314045018100d41d000c282d100b40e00e0014600c91 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 348365188 1250 348363938 348363947
    0x2040b070b1e0637122006030c0702010311070506060f030f1b06070f050d03150b1204230d02240613020d020406090e10030309170a0f030503040c06050c060c0c0c0d030504080d 77
    0x891000800c800c0c08d540c3c8a1a0702007040d0080c0b00140d04058a5450103943c0c1c07070004d0001d202681c0550043c005914090701845030001c04809454041d07803041d0920b0309003078400b01d002240740c0007905016152106510000d00540151f0a0151061144040c0c40c02001400140015041007646051088801700e11240301040001c0c424110310b00300070041410741800710340344a0340c05071040844c3c04a820701ba5400090800b0003100b41c500c698825200704140940400154525116001603940045518541100c0580303020b00180c1c021111100196110700c083d40658607410b40c030391800c5445682c0ca02008206101c070b403180c03012088640011604865a4042d65000d0326015115000c0342490103030a407003078a000c500428540d005140c40d034800200d46001c0e00d6100da0088c0d036900d8403030400b030030040c1d5200d0a65004209001c400c000c040001c0c0ea01088540c0d0009070419401e40717428006c0a424201809050400d9010080300c83e034600301500500900281d41c001c40442e881e4170740d030040544 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 348366438 1250 348365188 348365243
    0x703050d02030c1612020103110d1b02010605062d070609051b0105090d1205040305060406050603060601050c0601030f0206040306020a0f0201060b04051c02030102040b070b1e063712 80
    0x5034000800d861781c0954069081403211014620206103000c1036111410215100706e0040d5401d56501c5418620303c560900450014050458400e880e211402c034581424102c0120744032001106202c2a20078031881c541a0b404294100b8024058500d040c900b035512180e85544580c40d6004042c842c0016511540031b40d10b90090207000302d0700110f4075444840300300c10030100e000200541008003000080050180d24090741c130400b004249400c1c410f080504080c0002d00b0b00e41003000604c07038a150f0010000b441d50440390420710b0410340303a00500215407180310b142c102400c001c1c0001004a81160b00c401100340c4010700f94020860b20b0746a40e41c03905503105d90720400c0d900c10343c1c40d40d136003100f0f160b005510858944010300061030542d03240300b500d20741e0300061010340f10010000100081660060600880d1b903103000f60404103072034540c0004003c280120102c0003810000141e4107030040c402003011602088031051196500d0b40c800240280302c1806404840075591490030702d492009542c00123 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 348367688 1250 348366438 348366449
    0x12051005010804150f0c030209090c030421030902040e0c0f010305090c1504080a0b1902120a02030702070302041503061524020313030804150806030303070c03020703050d02030c16 79
    0x181c41d40c0f1581c030348012003200c90628200590751441c20080502e207600c19103003800c2158401588985141e0100480c0003001400e0700c451030410010080028001c6d0980307030b15001000b200c506010b1348840200c0007040c1902000b504946808011071080d040011040403007141142d0744080d0f828104011015102c044c0d5683c0720a41c170810881d9000d251400c0202046030740304062038281542c0302c504a14000c4401c0c01524950590000e20180c4580302c590664001030002065160500c0403200c036023418001810000d45640c040003040105100b402000c004640023070041c06140c09000da190304014a41c402101d10516194000b06030030440400c400845016000184041c07086c22682c819441491079031400b1404100040001c2074144108034000e58010982c2c5900c680c10858003800403000200300d101800350072410007426960000459911058038038124000f6281c0e498142e00d0300780d5680004102c0c0c06400781d50054a13500001030200306c2a410102c4240ca541c80c00c0000ac109030a000700c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 348368938 1250 348367688 348367697
    0xf0c03071211040c0806090109090c0b160c0b09010e0a151103040306061440020d020c0d0e0a0308072d03090302010801081902040e0109121205100501 66
    0x1040030054a460800c02039029401c482d50090000c1c0c0007408451001c981180469200f40510400381400700f9410b024107042d86003041070b500c0948603583e0f20385003482040c081c1030000404141d600303a000c0107044600e03400100b404c80580c5540c0c00403034503000000c2044c0028408400d0000e00e00e0846059401c641b00030002c0701c0300031481c4008640503d28692039001d14030041000200195403881801c008005001349007220844040c108240c0c8410b03858040010f0186089100520700f02c0d072510781c0f40401e504180306003c0e00d110b04101c040d01441d03400b030b108144040307000110143e0200d1031030b00368a501c0e51541042c08041003000b001c0c02c0c0c2d0b03000c040c1c0b40c40402d1103400001917607801e603111510700480309410941d50f01007882c040704200038412400148844c1040045507046020180036004140c0a01a12903506605d0704110f401d003000070384140d07121025091540340c20740c89080781d160131103229070260707903c00d03000360034801c00740020040645044009180906900c22a40584105070f55 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 348370188 1250 348368938 348368953
    0x1202070b04080702040b18070f08010e070f09050d0c050a0801020304080d020a0507020d050a030306080102031311040221041707030503070807090f12060e070f03030503150a0e06030f0c03 82
    0x20b550040790400e40d000c83e002641c0d8100c00c4036a6a40500c4c0c035264403007146500d038480c0b4040b000140a020720310b000e4800d11140c04014850882031020181d408441c42c50702188009110b80b0445403842150700c1690040300d401048003e008800076403600380d8100365820000c10f0303520f041080c00c074807003224042d2007154180003003c1d0006aa400402503005030745042070070300b485038002070640050300d04115520b0380800e12910400d90980604001030816034021411403405603500c8510303000c0c5240c000c000310315190b40c030080b980d00c0d68155008481d640c01c500710b0081201008003506074058506882100800c1200340300e004c200c1c01102c100e168907913282815a180c100303055800080152100c000d01440c0c80000c039030065920104402031500a5072030720071050a040100441d418550342c407586400581003802406851440354040f00e6040ca803c540d65510f80c001c4040d079117000c82d01c856000e0300746000001e40c080c4041e6501d0144c81d0840554043c804408500c0d55542d4210920a805030445030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 348371438 1250 348370188 348370193
    0x1d0f0a170a050403020402030a02180108070207051005040b0301080105010611010615120b0909010213060903020a0b0a0912050703020109050103020922140408040f05010828060914071202070b04 85
    0x50141c402099103050050410342c4a03800101a0780045030402c00540d4046080008288901e10031103c0040a003450710403801c01d140c0c001c0d03e44516010302c0b4011038402c00080f6030144114119001800c4803504580c072961140c4c2214040c102c00e204041c0012400306920010344418803450080715071140303018801c000c1e44881030350060311070411130000560b201d807148241d85070640038611440d0208001643c681d91040320208003120b07608520304102c0c03151010f000603140c10403101c0a80f1481759101d03442d40403010301100e00c1c0e401a001200d1b0a8295208003041000001d480340540303200f603c0f0315080070b4451004404030f00686d10010390001845860300003040076a440349105160702c2e00c3c0440c03840451f0060010101c4181ca00f25901e4400103030400c601214882006c0280100b40703003100484c28800d800400c0c00c0d01c0780405d44109004444800c0c080c2c01e06520003002045006002d00040d060700c5160000c10301d0407190000400d241c0c030a0f903ea074010520803030720700951101c220a41904e858 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 348372688 1250 348371438 348371483
    0x140103090606090c0c0215090f0d0206190e03100c0503070c020303090303040f1401170a15030b0f040b0a020f0d090213020301080703061a0622091d0f0a 67
    0x406081c0d68055448001061407680c601501e581d899154440301c0c5441d0480c03040c040000e40e8028207801050707060005503101d82c1c4440350400600700898000365500c2c6180000782c010300c107a0880d11440c60a2916036541039400c14060b6821032012400d0f103031008104031f03001d010740701a980e4400c0010410400200c0c0d01c5e002e400c00b81c001034009002c4a0500700c0000100e890b540c004d800076826400ca0000401c40c6a8020400300360404003884c149805e000d815240e041d070100b000e0182e4001c107455060f182e8020440400d1007000710340010150450b4100310200c151200c0d0251006d413220820030000400e82142c138000c0790f46109820421a1070842c4c2030300024000e0124801c101c0e4065240044842410b5aa0020354041c003845005001100d00e103240042c122900e08802c1c0d5180c800c01c0903101810f5448002360340c0e0b10244c0300240f0a4032100680e0103080b4403038580081c840d1614024ac41020200424000c80c034140002040307070920202c1c03c40c480da50325007403d0000c0014152880d091000480c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 348373938 1250 348372688 348372701
    0xe060304060e0105012601060303142107030c030506030601150f02031207090608070309020f0d0201050d0903021e03030105090a020a110703050d03050112050705010806131d0d0801140103 82
    0x160728000394844400c02440c1c02c2d10420303404212044074001c10419190b0700403800d001000074400003004034603e15503020340703400401050540b6040300800c0608105070700060f140ca41f0f449207186000c8601e4010f00150081c14000e0030000020300d0034000950300c0c2000994141600c40c0400300301403403603845200315880040601c462045010074844032105040001c016405848079480e19507185017414001004018014814002c03d0b003032040050258940401c071110205080d1642c803000c000c1f60005031094030440c41400152407401e13022030245507010440c804030080303540c4032403003203061880c4683e940d010a0144550040c0e01e000803e03140081c603801003035480501e05102a403e24801c00917420080b6640c401c0c1c03501d030040c0d189640030b00d60611905024040001d01d04188095a07185c1a82c1e4540b5170049074140b06070b210201d001c5644000039030702000d490003000d00c000c2d8100440039005c0c1c05181c0203441948107070403208041600600c00e140c1038540042030117405000d0709004402910381c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 348375188 1250 348373938 348373943
    0x1215010210020d020c06090703260d1a030a03030e0106170c0f120706090915080d1107170a0b0f0934060807020d05040f121707120806040209010e060304 67
    0x1820405117052600034459144511070081c060300484d03145007060b0490051062010101e408590300c0c0c00300035031546040d2124070480e841c0004032056810f20405122030401c0341303150300d0302c100607500701010740c5034100180241c0300300c2c000e0211a0740c9000822440c001090790038045d41018064142c181080010b42c0c04d0700030010007246080b408008070509104003504680e002619624040c803483c1202e0040398260b8400782c100f088640d01c1d1541940e01c400038640c05000f00000646102d6005030200030700380c040c00e55480d000c94501e01e80134006036a81c0c081039045a0440310100010000d201640c0114843d001d0440603181600010080d0b10011102c0341c030184420201a090313402410328090180b014044a0f115600c02c2c1c180544083d10301381d01c0170790140400c501000280124039621180b1002c89070701090440c214000b5141824500c2c800a610400402c07000c1a680140484008829101e0318143c9030080203172950340502c400da21075442c1840c0800d0408103004003a040003002154850b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 348376438 1250 348375188 348375191
    0x60302090d0308040f380103122d0309030e09040f0210020f030a0801140a051e01020a1407050a211101050d050f061206010f1e0b0c031215010210020d 66
    0x5d02507560b61303902c0e080d00442c103104c1c0380d0350080c800800700000c1d08090003031048403e080e403250315507030314460980058803000b010895400c0c20541064111241c0400c07003010203130b40006060031b03941d0050060000c204280d000800c50094003105040040071980030315000040c10031b0307032203a580a102c05a0710a20019085105200d0002c0c0c0800d001d0000d4049003a65565140d0194584944082c240c0450300165103da942003808202c0c82d9a100c207840c00e4160099241c0404008510050b81840c13000c10001c0c2144880000901c0c0c8031901080c0345059841c1110049542621403030a981d426000e4280e01c04116842040c42020415510031075154080501d403191426000071407650580e8002e13502c41425641c450140005880c103807428460f1040c2440c0205a80e40c5010300c006070f00781c0d0074401c034115095140540d1616200c090f40443c05050f404da00ca5542e05035901c0c01c682c3d241d20041b41c03031f00364603244400700707602280300c04d603d0000f41d1050780103028000041070442c0c002d40c4540d83c0340c078249 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 348377688 1250 348376438 348376463
    0x2070305070f2003030901021b04140a140106082202040b060d0504061d0327030a05030301050405060a0509060906041b1716140c0102130915060302090d030804 70
    0xd01088445150948146801d08040c030b2840645104808140f0700710340309400c20710000d807099038001007244d600c1c4002d440601101d080c0f140420010070401c40c3e00300001e800e035420808101000c1d00419101d03a241c104c2074180f6aa510f0713085410315015070380c00c02c140324118003483e440070400300c20203603807800280000307880d01034400000c0095000282c2d03100901d4075002044207100c082c0c801d09040440034200f66a594030050b414540300c0c031884003d0300320050507042185c801a101060000c01180c0601100d043d80050305203280e61760003d01c1014810b504001c00038031130b810300010f0300e800c032027000d0544212a00c42104100480030010905070700700f5601c0203480300c0546201294007480c00e50352034100d6a00b0a10b40d0440903501b00404480e00d01ca0000e90011040368003d001403010030b850f1540030749072280b001440f800780c441d000b400801e58107800e401107807800c0980d1114500480700391085859541d2100c050f030990084d00e46c051340c002601a07080002c40e00420108c0d9016118103010120f030b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 348378938 1250 348377688 348377693
    0x61b0304170f120918100308030c03040c1a180301330b160206031306060f080d0201090503041413020414010908030301120821070e01020d1707030207030507 69
    0x340c060186040c007840d030044081d44180501480340c0890151182912480d1802200103c2c581c0a03100c00c45044000d0b0750b50001d410204c000c0c06800182d94008910b13507803070403c119a90529001510309549044030303917200050440c007910100d05000400b8030001d04008000b100c01c40c01107400303001103030555250032950510003d1030056410880c00f24940d0000180680d15032010300800b0340100080b90400c0000740001030b40364141103411a4101c8120f640ea64990320042c1c2a60720010b002008642003460114010318000c41160a03585030324100c030100c2c3d400160403428bd400d100c0d03000d002908200424003c20382c01d0003580014980c0034020b081c402105c0d8800c8012a881584501c440500c0d00b8030005a66a00a0603000140099801141103504202560400c11a0084010310300c80700011000701d900d051480658a0010b180f09001c8145080749000d8000c090030000d05005001e41c000b0400100d000d070750300322662074441d0800f03101ea54079504103400943c811704042e8144102072041000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 348380188 1250 348378938 348378959
    0x90613061815061502031c02071a0103080403120507020f0f0a0f0e010e01081f021c053d05060702030102070512070c060801121b0f03060504050c0a05061b0304 70
    0x40800140c00002945131034409003643c5909030321380d90b00464004004454211031680131103911000d0034000143d0b10081031400107101400e101c600c01200b050403000106000c0007401510860b401031100c40d0065405543c11140c1e0304ca1010025030102e07803204001c240d41480c404c055860b25001d010314008640383c01c402018016594000c4d11020074900060040d0701c04889a00d0061050a0003404031081d5070b08001c000c4c51543c503106000c035601190f5290700b180c907102e09040200340083c0070812420305d0240035200007001ca2040c3c080f80d44100d8000d40030924000801101a0101c01c4140310038142010015198450401a43d140d0740030702c4502e011401c1400015003042d1404a00e9640d40e5442c82e140c030800c20300d80d00c03d4046c08070050040103070110000344140855402044225503440c110346d03e0301060101d40119a50310f0345030002008011203603100301d000d940140d044030085036101c010030003140440d019071500a00140201da00c040441c0402c030382000020b105072030805445a48098 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 348381294 1106 348380188 348380213
    0x1404030519030b0411030403031103010b0d0902040209061908070c0c0902090109090e0a1b032105090d081b070e010b160b01120203060906130618 64
    0x300c8861203903003c80f81000c0018010083d0600d41c039202034039504101c400f1004a03103040480104200000283d90481d8601320445281214211f500c4014007242e2104a8201d502400504016550100901860103000d4502141c50821b07090080000401508110500c10601724070008540c2c041d0388281603600144015940d109180b004071800400c56024400d01362414042540b000c101003040007909002d12804043c3d010858038500000020740300c004d01006103151803180d5480c07056010b90202095040ca14200791700c02010030b41590f034282d4200c407007200000344036000c9602c0909107035500c4101c8004154581c00c01c038052036140018096071704140404540c0c49102890400e0040c3c003036501002c0c008095031746a03046025043d514500700d201780681c10004140c0b110014041d40f2504a0801c8044c403000340b40c9440d4000c3c062100244260b982510281e80413036410071800 = true := by decide +kernel

theorem cover : BRFrame.Cov 348201438 348381294 := by
  have h0 := BRFrame.cov_init 348201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 348201438 ≤ n) (h2 : n < 348381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
