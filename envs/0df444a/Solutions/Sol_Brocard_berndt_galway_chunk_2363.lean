-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2363
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:29:11.272984+00:00
-- url     : https://prove2.me/submissions/d60c2c6e-fc78-4235-beac-25b76a3d8fbc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 424820143 ≤ n < 425000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 424821393 1250 424820143 424820171
    0x4050f04050c030c130b0307080a030f030b09160f11100c0e0d03140310090501030f03031401030c050d0201031b05070308010f080c042409050109060807051c24 70
    0x202d03002007040d030181c00e4400050010541035062034004205064946415030034035201004032400130840c03c02121048040703400c0181403c500d040f15280060305064a9840301d082101d980c40c0110950301410b54000340c00700c0101e1700c0c007010900702c2c810007041c06000d80c050b02c405c01100401c02e03005040000c3d6940c4010010b04141c540d421043d020398444034148002c40c0e00305001d804500e5031420410350325503494400400300410341d040302d04024501400841409903150301360f41c890344240c50401c080070520101c0170600209120041418038040c10500c210300b007401a42441d0b0f031043c100896410040e840990302c629031241d0304400104040390301c0c0e0074980d0056103a4014040d82d00c460040906008009460300d500080242c0258ac440000c04d01080400c40284c0007a84a289155000b649802c40b86002c0c2600b0f01c2003400b41410b01502054070b102c04107a601c100c46004007a070100010003090714035000d054a81c1681c1c000d03100c100c103c002c401e503200d42500b03428580b180040c0032101c40e10f80c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 424822643 1250 424821393 424821403
    0x80c070602010e060126010c1d0607020a050f0a0302041a100c0c0b1b01050f100801020405030c0f060c1b0a090902030a1b09110d1103060a2304050f0405 67
    0x42103007168103044102a4100001c510b8a0543d40d543c0705010451080781b50440c0c8054072440062590340c80c011100806561042c010f22089141909100602c804501040824000d03580c0196200080c500c0401c070b203152416039400c02d01e41c00741c03030b000c52075a032a00001c046070100c4070400c1e01960b002100001d81d1811241000c41c1c1c0741e680c1055002d03541661240b41c1081c1c2d80303001c0e005101e42d000400d00101441200848507440c6040000d0015203020118010700180075151110300c2d84083d000410b40c6081070087d1010313a070029000b003440318043c5041280016044100711f4004800300981190070006201e241400b031020055401c180017058280101c40d9115408030b000545860003600069402144802c083e54003c40381d00c000700d00c03900e000080503500b540018030081c9040d20b0140e00ca41308038003620b00c042d8860320400900d010760114000c01c0c8011601b45900c4500d100050011030140c00c0c1758401010418280301c07100000401041c1103a0041e9590340e4403003138107004c002c200142040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 424823893 1250 424822643 424822649
    0x12060f010e010308040e250c0b090d020c04150504061220010f0c05100510030c0b0f03010302060c010f0515130b030c01051806030a02070c06030203060d0305091c080c07 74
    0x10a51119855521038041301e000c0d50041c001c0c0603000a01160701c001090003442c540401515425040035034408000e0581c046c448001c075103074201500000c0031103101003035840340240c098006c0e158040d130070720802000700128501c0d100c95050103500491152218810480903000e41c0c14440e41c40b801604010a84806800d40ca110520b8101041000c0340d9102c0ea1f10130038105141031140105590346402400c090011503202d024a1500f82006401c0301038012007400c9031b00581100810503160704038070300e4074450040c1c1108a0281000100014105440200b034803000c0c1100000b00e03400c1500045094a0302502c01582150308200015400d02e810ba20040d032901001ca0304111010918001c661911005400581403000c0410b0001030201d01d400e19400303441008110f2984c1c0d25001d45410000d4020300016a580c1590420200c2d819019100301c80c011000142100b90070103469604403080c1e4020003627650809040702e0080050311401d40040f2085d4810440c0c903444060800b4600d00e45041c5074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 424825143 1250 424823893 424823909
    0xc0601080d0504031e120203090112050f040206030408070b01270c0f08090118150e1203061306050d0c0e0c0403020d0b04020a0b0a0806010e0108191a12060f01 70
    0xd2405070403070304101200d0443e50f00030700700b110800d08821a130012502c130030b4019010210130740c070030086036601000419000c02c1c02d88134401c6281a88120404039441200c0e544004080c91011a0151620602640c0d019124590040c40c00c0200e659128120a00381e100c0f400d4600f0040c0f141000140360000c0782d4200a0701541040210201040149105990000f040a0004c07a40208000040a4000408a4031a0f2141e80882d458524080042c0c060000760600514509014100120f9000c15400110b500c89000386081d0b07150b090170445641c5813148220b0140741c2d100e80018094886400f641c400310f00035010b01044614103510b0905080004200520f464001c1100780010381c4d410307841024103034004000483c9d40c1d0712840132541003000c40d040545066004180040500d0b800300001d88290303003c1e610851000f1200c0c0042d07403049400d8030542d00040c0b940500765003211031076204000420039141988240e1403032101041c00000d09200e00300444c0c00090400c0203a20013090314500409200c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 424826393 1250 424825143 424825153
    0x31b0507050c040f0f110d0501080c030a0b130209040503070b010902130306090c0e010b03091c1202030a09080307020f12090607030f0e04051003030807140910050c010606050c060108 80
    0x40d5403080e4030b803021000e0141c072455850241441d2082d40758000c000000780c0d000c00b001407103912110445141c00001002440d40e08010010031456804540c00100003809802403051007155940c4503013102005140d03649061b0340113450009071f956102c1890285000704055039039402c1d0360904103401c800c1600103203005801001100d08040b1465043e00807203800920016801a00c0d250202081a0710f6016500f220005030000c500944c041c00114000c41e43d1508980c0058103958401641440c10b228103000701b55041d59000c40703150650021a88900d22000005140c0d4003503403005d00681041d288800180d00030700310400c202c0010081d402d40912001c00c100c0c2408240d6000520502c41d2880050410074441100e120080c0181e000c0819000018130520807868a80103403494041c031071100741c0004482e0004120395034042c52705e0084c004447c80000d0700e09481d40090003c129185031000c000c104082010040300070081c071a64019240d15521907940b22005103d05280607010b07004043d154102c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 424827643 1250 424826393 424826407
    0x306030c010f0f0f0c14070501110a030c14010f110a0e010212030403110708060408070204111804022505010609060b0f070b131b03020102210405130207080a031b05 72
    0x2c02162a041d80f11460702d003e48032180074085a99051007900105002d210450032804c20340c000c01c502054803000e07030b9001d81146401842641d560702c110400350209400040145c007250840210805600c81a000840c4146018017240211100c1c4130b0340040440021500400040e40000c01c089180380920040070b4015401401c1041c40c4000b810007024060300002c02021302e0000c0c07103100d0003000300e60150303459490541000442a8002c001c100c1c41185081314801d8109014000c0e2586603282d0811409840c905000784030095015100990550003940030421103403841507104045c03103204d480007041703036407130100c80c401507800d1504151091700c0d01340000d4550404480a6440701d41c0c03c20710901c11901d031440414904c0305035510191980e010240c450b1070100075842032500b180d1013a0f08940c11907400c01002c0380810310b4800707500400001000208054a065641c55981c105642001440c2201c1ca030b540e01c02c5603114543c5040401d80300c204079151041d940106040203603050130041c3c5071043c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 424828893 1250 424827643 424827647
    0x5032d0d0905210d090306110307050711040f020a0c06050702120d0c09050603040501020714030301081905010b300109021804030c02060301090b04050a0c050702060a0e04110306030c010f 82
    0x3180a00781c06032125280c2030303006019800d1100f0070468007009071070320100c454130000e01030311882c002501c4941c10080720b00d000458484c200c92281000d40d035100d040044940c4c4480908140039140396206883c4ca144080c1c0030460300c01008142100d03103800c000ca01c01490b014094400041076241035412011008401b0010002211441c0807200b000040c410340b8540c0a81d1603007a107170025600058080100800c1241c15401442130f01c0c0542d903585003511451007030503030301d100901440c4510b4004400d0700c0c4140500100d40340802d0720490010031000d4104d404112001a00240e6181c6110b024400e60b200c0d08601041150000700f8000907c5062456004a410800c0c106400c0c108400c040001a0505109103800200103500602c40341e5203507500c4104030054000400c0c1e40384207910700380c00b10b2803031400ea01c41c011502c0d0560301c0707644c2400b40903000c210f402d80050150b40c0a1124400c1d0700c0f0b060b99038601c940b000e0407c080c00055201d05041c001d0520f00305ca4000d01e1414043c0040ca00d541440d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 424830143 1250 424828893 424828907
    0x30a052d0f030907030501090f06050f0601020309100905040f022502010e09041a25050702180c0c070e01140d0b0118090b01080a050607050703050d0207080405032d0d 73
    0x40c0c55a00e49a0301c0d26108111442c1c100c0541c0b001e461b651800c09480100300340341d42c0300b041c50b5029210602c4940c84941c1005195175080d82d0050140e0700802c070090445c00d01c070003030300080f40d603600b032010f4101e55840118040e544441d04a04585900280744502941c80912180c041400ca4008480071045980040c080c200404403507031281c020440094100111807001404040c8075202c0d110301c908045080301c812903090400b100100c20000645a00300703204109444406800801840d40d41d404000710018240020700b00120780c80d020003602d280c400c001c00c1508018401c6009529282d0315240920089a4500045034800c4184901031004110010009415901c41d1a0403254066075014100005c06c01c1c090010400c00b0242c000089007000071800f0482c06000e60260303a00c990b100c4500311010301c10700b02c1c024003040d810b1103008035403207043c0d02401c241741c4901003040c80c00791030340b0001b480c1444429107015440f2441c1d0404025281443c40d02122030780c903000034030000c800c090000d4904 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 424831393 1250 424830143 424830157
    0xf060c0a0513150c050d020f0a02360106030605060a0f111e06040213020307050d0e150103080d0e0115090f0f020703090e070903020a1e08030a052d 65
    0x401041003600002c12004a4008080100c00000d20201a820150002d1042501900d413800f80707401c01d83c41d060000c66042070340c0d0511005070003640c1c659801c000c0c050400175651085000640341000312048081214400405001814041c5616002000b0241c074410b4009a001d0179040c0400c601d00e039001005400d000721a400c004604d0500c1140c07041c6010303507812644a06124007510080c01d500301040081c0114029181805000304507008c04c000e1f84007c2c2d5090000643c2041501c2d5019004e0b808440e0f0846541c0544034440c1c41082044a04803081c1c105581d034020004645030b0b0f00e02584030b002c2ca144291402480070070b5060b0580c1600100612402c820184c858505c03c11103452540300c02e0014481040442d1260401c1c240208007008500422080804201c049881c082c000d80d51082120303030007413441c1d039404d0414444140401002c6c18807400120b43e41000306031030b00140080c15945140d43e94480d00c407140424024502c0d503220740101040400c00801065071000e0104484c03403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 424832643 1250 424831393 424831397
    0x304080d0b011b02090a0b0301051609080102031005060d0e0607030203181507030b0a03140304150306031707030215011502100203240a030803040f02040609051306050901021216020f060c0a 83
    0x140d8501b0550800b6144140c17100768103501e824108040c02c043e100ea910501520342c4d50305101c0d00d4a41101c2400c0384011340d20502e00c0704105d90100308a16191000f48000d0f003620001203080c0c16000b4045192010030360703044000c00c2d004410800a0603903603030480c0c51040c1c218010304824000c15000809040c0190400c0c08054450103030290030303207500e500e401c003c6500c87c2400c0260f100b80301e505510381e0850700481c80d0b188024005450710610078002e80003501d421005c42d100f00060305103881460f6210300401c80075402400500101d5802c5100524001d00c085542c220101e050050024101644441013021192042c0f00b0301941e0700b505c1d0403031011040c0a01d151020794810710009950701c0d10030790000b42815070020422003008090308111101e80e20a40c0c00340314046d107400318001504c000f22002c1040300c1c851000500424041d030010354001400c003000601e4013030043c0a0494026044501202a408844c980e01c48141d0401101d03008030040c002900c541d0a10080c81c000c1b81c85182c5034101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 424833893 1250 424832643 424832659
    0x6030d120e071205070e06090c040e0a06051206010504060b2805070807050705010f0f050909040c050d0303050411030304290d06060f11010e150405030904020304080d0b011b02 77
    0x1460220800010001c2d03d00c09031207107048982d030300e4095907540e181d0040b50305681c0403402003000c9042804845008041041050b41030078203040c010780c00740c2401821003103415201c600019003501c802e410181079000c1c030809060780c1d604185c01d200c2554550303844848245403c00c17441c5520b08130b0703400d02c00d03ca40c5078480c0c1c0d0000038643c41c3c04440314000e040010b8119440003a046040010002d1040e00300d900a032180c4801e070400390000d4840451441c0c01c0c04c0840c408109200e1310745007946400c2d50080c45480071102054440c400b04203a04540c441c200d020a56a80a000501c5143d41821429183c100c1c001e40ca03090405002084c50801c3e030140d1044000e042c07100c51146070015041c1d90070030a074107404100043d47d50500034000e8211140307036000b04c0d0460075450001e42d0180210181444418000d081c0b580224192028081d0300070710a030f0b0940418085080d00369501c4c002503004074002c3c04400d442c0c1881c0000c110840d20358020650502102500d900d0f5035000b08500040901e4040328221 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 424835143 1250 424833893 424833911
    0x40e13141b0f060c0d0c110303041203050d1e0207051501080c060c011404030e12070b19020a080706140109090b01030b13210210050903030c210c040e06030d12 70
    0x148071802180c0800e0045c0c001c000030620810760041e5005035a40c081c00c0310345890b01300c1c40141612072059009806151480e1450840428044c4006050070450b9900c0001c0c281e84680c1d08920a011000c0004003e07a00007510300180001044000c070b00d032017201c2c08042c1551500c01d2040d030320441030400f80d02840000c1201c242c0003a00798081000443d011070401d09518091400400c0c802c070050f081071080007002d014902410000030070b80180c030148030100e89001445200445061103005000c41180318050100f00000c1e541e40141c48094810040880c60036004641c50a1104050b084400c0040c03501419201040400f0180c0d411a0340060400c042602c83c841c007419141c42004000d41610014010301c8111004002c180840700450343c00c0d200300034aa80701c0c4206880c41558141c0f4594010700110b1303059510940100745c1ca4000c400c030243d49011090b1800800c07801100c4002d05c0c0c200200b020083c032108104029804042140a006803e5100c1c4000e00712a10b800c0c034407903540361303510514 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 424836393 1250 424835143 424835149
    0x31209061d190b03040f03200d03110409020c030a0f0c080d0218041514040204031a070309140102040801060b0c031c060b041413050609040b07020102040e13141b0f 72
    0x20010b8940d00f00001c0d640d282c18200001d0212144a00b240080c0c42c43d0b8451045140c51141e4050403010980601005039000008074050100c0c4c0517141c0410500b0080040e01011b10310003001c2c000750b48000b940d116106100080c2c0702c1c0140300a5281400782c1d00280e08005881a0102c540d1882c24800058444080140c044030407440e0200c425040351920760440f5400841d1500300c0115001c0070300c0a0781030b0580e0801d1109a02452000400807581a1020b2001d01f1a185044d82c0c0000185030008540240c1d07184c9500c1303801d1012110401da540003409004841d405c0c09818050080400458540001c01550507503a204115020ba9050141e404070f20130301c03805070030620082902144850b200c2d03445403100b00d148030109001078410074001012191422283c0920303442418001d040003903e599945500319200b4001b0501ca085540c01c00001c07819114112049008a2032085103e006682c0c03880c4c0703d52170f4205024001c00d29804064024a4864100c10220040c035080d503841500070008004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 424837643 1250 424836393 424836439
    0xf0a06081005040e010209030610050307060503062b050d020106140904020111101a0a0501080402010c060204050907171015050d140403030e46050601031209061d 71
    0x3100d5441404c0c465094507080b0150043d000c0ca00e4224140c88482e1180c500750864041144941a05038110071420080b46004801540c0d10980282803148900c01a060521060340d200700e038280c148900030b2065050240c10006160b0b0a081030008005450030407029803060384040880c244124031100c000780c11a4868444403103224940d2003202c54031002e810500000c0c084900c2d00c0c400e10651206c01c1200c9141064405080b12010385400e409510386400445041390100015a100c030740800c0005410307200d01903914071850103591030002c44050721041c00c02000b40903004011161141d1018042400c00091343d01c41d6512a00380b9503a11060801010060031402c1c04446488880a08000a00d07400d60800102102e018040c0c8514589401d100c10b0740d41c1501920180c001c14002903002801c161188184210440e505d500c452074981c0d558a500c0c1c640c09030403c40300c4203e0141c000c0101038010309401c003d4411400c2440340807030307460020348952240345580b40c8070721031804400a0403414045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 424838893 1250 424837643 424837649
    0x10219020102190506070e010311161406010b0405040b040c270b0f250c0911070501090f0204050a060302090f1519061412060409050f1f0b0f0a060810 66
    0x80384015800700d130901e2600d0711000c42e11880440c10781461200158803074800d04410744940301c2e03114142680004416504e242440d0b0441d05c1282e028006103004034204080ba0080c003401c017800d66520305000501041e10021084a40684c2c1000b2540409030f801401c242644922a44c1c921007900b00c4901c2d40c8228582640b1003540380c02c00103610701c01a00824001c0010700d00c3c40c41841382c8114629500d020040e0a040098418100c03800103000c1c00509812510300b59484030038843c248502c94445a007102c3c2c1c403900c22140d550810089104506142c00303981d5006409503020040c03a461034010640610000f0510b008080e0308000080000350308182e8100030003406000c40300690031190080140036914000d8401044103102c417241c1440800044544144040510380f00039240d620a00c4042e0100c100c04a9035401204040c1c2d040e007008200c56183c042c0e03d646941e082e00ca1800603502118200349842c2c0c018040e2060f00c8029860716070a08044901d14a00307050541c1d1840000802ca8006030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 424840143 1250 424838893 424838923
    0x601050f04090615020708190302030724060b160201080606070606080a15060501050f090f0432040503190c0f0803220507140f04050405160e06010219020102 69
    0x10801086030a0941e1044003512441d80b0403000c0000c01340ea05985e10000c610403445158000100d80a403252400041c2c075803079200740110707403c1a04544d0381110302c6201014080b40c103803050203c0c4440303880502400c0c0040c0684002e4500d40300c800e21101a10201000c8040e040c000004003040701511010110f0740c84c1504a2070410603d07458804cc2601d40c41961801d0342c008110541c80340034422030380708150032604140c40d21490701c21620040160f40d00031134207140e8060030105610b10b042d115402031810741180d00401c5002c503a1007259100f9102011000c03042c1c0e490480c010400014000001c54042d030306940c1c00042212031460b41107510b4601040c000f0240c079002c07030755801000003040255018a0820070f250f11043d99220702c8201c0440c904030301038030315403115200b000504e41c80783e5503024031440030700b02079441d110007070109094500c01d8404071100c1e0701c0848200e1404103420303d202c020300441419a1014209000002e650b400d4401d1880116150741152a046a00030400310850403454 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 424841393 1250 424840143 424840147
    0xc0c0b090d020607030c170a0f06062304050d0204052502010b010e190b1e160515040c050f040207150506100f051b010914060403020c0a080a02090601050f 68
    0x4400306488220340704148025110380b002241d8024040d015050302c085a0b580c400301d48080c054005451808040d004590850382ca112424000c034140c019100030300380c0c80d20344810541d00c101891441e4170b0b00304551311f403140c014007013481255036605141041e560112070204840d119201410000044000604c03c4c2c144000f5210354070580640000000c20804d0321440e54441c0760b4801c0c0a1162018940500c02040400c401c0c041c400c1c20f58080c258015184c02c180c01041c4a1050420003507001c482c00c200351403030102100003080340070880d03184400c4c41c00004018600342a0740e001c103441e0740750007a01e101c1c50745031350b091219845950540e02c0407500700502202c50007140a44000502c0155002d81c000e0fa0001107003903c241c0501128000c611f00d0b5502c50b46040007840000b045080484980f070380b1952211100c80100b2010b100510404c10b1081c003406039800c2a25006c1d10700102d41e03102034016200d80c441000b807110042813410384140c0545070075407203a86020040368540309180690b6401800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 424842643 1250 424841393 424841401
    0xe03030103110406050405191a2205161b020303130306020316090503030d05180303040c0e090705010c02010e01020c0a080f0105060d020f010c110d030e011803080d0c0c0b 75
    0x1e080c0c80501c40c54000c1d2030401505407a0001c1c0f00a0ba01c0490384004031b03c00b45112800c000d008d95100442070081440700c9d00c00c400d92900040c01d00c000c6582610070000040f4a40d1150740b440784030301c540010050907024521580c0d81c00180502100440840b014100d8083e09020364070b045c01291031041d03010052011041d168130304000250029103041d2500c1c075401802d0359256000d0662441135480083c01035060010000388403015000003081d1559130000c1c10711882440808101442c005e0344210b0000102c5420314000c40e101c40c2005103200c0d00c5a214600c20441a43c00514405600350207191080c0800d08000041c0e2600d480c030188160480e001000c001f6004002140c0c00b83c002e1010030090100ea03c50800300210003c104101070750041d8180300c0c44200e903014440390340490b8070402d0740000d05210b0a00051034801d44400580c0400c50340341e1404400d40e4000c0d0580312040b08400201c40b11403d60715541420b01940d034200d01d0055480007401c280d50f004442c0c84550fa64052004455460 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 424843893 1250 424842643 424842653
    0x907030209040f030207030b16110d05091c05070602030c0d0e060a1103161202010c03050402211203101a0c060103080c0106030c08010911010504080d0804020f0303070b010302090a020705070510030e03030103 91
    0x1c2790800e2000504040c090100c000b0002c128101202a155240ca0401c1421001c00c04204815840102c42956001c903240004009000308001800c41e6005582c9607a04810036070b003800d0390019080d0400c80f4030041ca000541e01d18007036138545540303440c0c003408a9514a12482c41e43c416a02040f040c80b070441889000c01907640c2c0054115051070b8000d00003240145e05c02d4060701d8050794000d502c11000c18003640c1118809010102101982003110040440948500010383c000e1b550090b0202c40d08005111075440301c90805101a6504c84c510b01e00030020113159101c2806000013840304100250070030341c5107000d420041c007542e000315111812580d505d80700c50007013403a854110b40c00300c05c401001a866004205403000c481501024080e2004014005c58000100801c02c071381c03207480c16a104a1545003003004c1c0c204184182010795541d4198010000c0c0100000c11381c01100c2e0040102500240b8003090080480d2002d544101108038860002d801505a01400540d03504c0003100002c2409 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 424845143 1250 424843893 424843921
    0xa0c030204050319022403010b0f04120b04200904023102040311120d0311070602030903070c05100c0308040c0503150f070e0f010c15020d02120907030209040f030207030b 75
    0x40c5c401c0f6040400d400c6440d40458850003d4014001d5081003800100018010340004200040306140024075154842c9a400540c68802c030003620811654000c05c0300300804074a468006540184000c5094070b44400001e1a524006100a00403045105030108000300c84000081e4115510b0300c1e206400300040c142002034215100564141c00d01c640548954240104003c040c24600009440c00701c9130b495007900a06411244051140420003400c1d001c2809840a907010308500406180d0702c85a50602c5c401e048001d0300b00c1232090600300781c10260b554205080c12590b44c2d05007000306043d6642d051a50502c48690320254150044522445110894000052280030040c983c0c0034507072104c1c030007101c1d40401e00c891103401160f14030352905950301410700710444600ca000b205031044481c2c40070078140c1c8c100300e10083c8030300c0c0c003c07600b10403a0700c02c02d02450340b101030300340181a0607245400140341c004019001804030700c002c40440c018503109010fa000919007041004030390303082c0082c00d11650 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 424846393 1250 424845143 424845193
    0x1a040c0203120a09020a030f110303130303020c0117131e03020105010305150402030a300302090a05220203041b060206010f08030c0607140904110a09080d080a0c0302040503 76
    0x814079000054241002d4400c1c3e80004d50082c0811055504607a6003072420030087da000c0c0c81030200d40d202c444490b941000281134010491030f001031540d02c0d500d4041d03c1d0038400e003100c6043c000465021400300702945202a80a0300c80c075540403458010b0300303201b925403009140302c1806940d580b40309004e240d0150800c5d4100c030300c25011140c08aa103030346460000101030760000d40c180c0001c4542d03004980001c0c802c180120050798030f1440c441c11900001d004050048202c1c0120380c0110340d00d03459207040e802d110000c100554120070030380030708640e0540c004001d881c04800c032a408004070341448036241002d120101c3c0c039551250303119211800650707254024800c0c01d1410f0104240401c00c060f012040c2c840d5800c00344010710f81515518010340d100300400b1851101d00f401800313541c0c11680c079401050200b410108440f40c0d070381c0d4291402015544182c1040c5901c1d03101c8414414a650300004903a0300c102c1560000130b005031000c1b400c80c0640704da40d00c03090b8984550500c4811035411342c0c404200e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 424847643 1250 424846393 424846417
    0xd0b061002120a05030a110304140f0304031505040303020906161e030503180c03010c08011e0513020d1404110f0a060c080c0307050d210203010f0302041a040c0203 72
    0x80208a0181269102c0607000b1000d01d18000b4040220654010005590005112440842d882a030507100211641080f2401d80b00109443d01e00016008140503845c00d454004002e14a070030b0554a07820040c0100e841e000030704907a120b0004013490300c83d605840c05604001d20042d5500c42c030080001040c07240000030f5400008110a24116030b01d0511388500b81545034580504650325912841104503140d0104261030180410380d0311655020302c11507000041d951a100f000d54100f18170441c103084038644015010303096210034042ca0303031013400400303251041c210302681e00e090603040c4402034080b483c00001051204d9051004102da110b608142d1403030251014a04a4401002c00250040f02d04c60304000c6005400703080f0108501c50010314104006504803868140c0c280d55892a10070254030f1200040d00124000d2025071444c1224504000d407031409506650410541900000c00c511000384940e40c1c50081099000c3c0384401401c00601c020010800c01100b01c40207901d99100c2e0105d440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 424848893 1250 424847643 424847659
    0x1503080a090509130809040603080a030609050c13031205160b0106080a090b01231003050403020d03090c06050903250f050a0e060105030907030609030903061112240d0b06 75
    0x7424101095200d11911300003191000340700081d201d0006644c45544826042030301d036803000c40171581640045c140d072400c40c3d030700040c8280360010307810403150003a10402540030f0810101910004483c0305505032034102030a000300e2000d030b0405456501c2100c0d0100d1078a08014041e02c1404910030915049404540b10300c0000e40e40d404012003250b45614000b00300c646054018041d005102e107124080200d4681c41658401c20840041c043d41c005482510020380c4800402c000c059041c0587c1d0307855069400c06000046a940c1c413800b04504500504040203000700d000c1c405558200103083c403200500007026440300c41c003031004034403034280d02404824090050001440d810b0140496003120095a4000c05940303511004541540c0041d00380b0105100b10035010010072102e2241d414164440c1e200d60008c2451450040c05a54040207801c922990600c482c841c208011017400e0742c404030001081401c291090500da01d01c5891801950700001c3d031316520341c10880d40b210003c1c024201110f04030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 424850143 1250 424848893 424848899
    0x2071509030c060b03070b0f040503070b0c07140f0d030e03010c050a050d480e0102150417161502040609060302073f0e01090e0a1503080a09 62
    0x10548509050040001d500c4501080100b140303540118136890004007603480042d40d502d00a080d58011504084078000300050820442c5420000e40e00180780c3e0510340c600f02481c0b0207119403200c0d102d10840c2409200d01500010742e03900d40b100030500710401409040c0204503400d0003030108002d920325501a40c40c0120310807801b030054064400701640e56413a07034035001c0c9a140e40005002c1102c1d440720410040c0c1c100914180c1d64100e9004400f1121210520111112071207140081c404c1f80343c41306000c0074154180503030341c0c08108200402c0c3c00b034680785820b4030313140382440300e1030034070100c00c0034407100880c0d61903030142200e4035440c819000f11102000380301c0b40d101a03c124896440f070030011402c0e01c3c0c02080014003a40140c00007501a03003000000c0c0a00d8601c455442c40c080c0c0307100756603f0b602c0500882908003100040003c140a1400340240d204c0c83e0006025540c1d280a200c20740000711001550082040d0441e10068034a0070681280c2990313840c1046094000000301400324001c14808 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 424851393 1250 424850143 424850183
    0x5040204141006031802060a0206160822020d080408160b0315090a090206030a0f0f060b0d09050307050a030206191107021323060f04020304021e01021f0207 69
    0x41c0c1c080e01c0b030040300c03402592a00c04113030010900d06600b5804041c00c9140c071070150751000060245094643c020300440d14200504038120b0b400000d07001e052002e4101804014102c45128080049d0240251140000d80d4000581500b4034410020b00c4410001004501c1caa804144030090400c0c461900c0012511107406081d64001164001c038811080d503810345261910354042a0889040d0b100051420515004505117a20480344e0b0207546450703204212688180d4819030701c000000c003100b08000d40c00c09080030503074401c4400c100305494070b80003000c090100501c21242040c1d801401c880001525240194440d0700c1140c0503440c400602d04200c0e119030b6103025450b6504903105469184c4000e607401c0240c00100c883c4041070542da02e440004401c0c400b9400d62005103610710300d5140c5403910340100401c849501c901a4041c81c01441800010f1b21107582105400d440c4074088641d60701c00ca00100d1806c0b0301c1c1071803510104150880550303480f0a950040c2481c50140b01e007103041c0a076032020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 424852643 1250 424851393 424851431
    0x1c1a040b03150609060d150501060e03160b18060403060b010818070b1b061305010b0315040b1302150a020c0d080703140f0406021615140c010207020d050105040204 72
    0x6209104400e001882c1480c10309132860380328000815000c40c1046035228a03015103000c40f08440f1442c1d40f070380103000c09508240003468414048001340000c41c520201000a0580303072044490740f25001c9038000014030f07001151101c2c00390141c5581e407070b1940c81c28201e016080084519020810300c8000c220741269030311651403943d45620041c403240d890310703c03066110761204074024040300181040140c14030302440907038007800196a07601040000c82c00c06c9421208580106840f9500515000c83d06103c610403041e4002d4014a01d101a07036a07040e1080c10b121120080250311140c2220b03c140b81c0519640605400d8015070700329001c0010900c240304a6446a2901a000036000c1c050240041c0c800d05400600d0310650038941c2c20301501d4910401160070035001000980c0000010128003a0a45000d000074207540030750040c0b807004814090409464411070a01c1c01c040001d0010342402d094044803c2c0550141405200301c0b00c50800500a140a440492045003060f2901d0351038400007007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 424853893 1250 424852643 424852663
    0x605040527030d020d05090606030607121a04051f0b091503100806100e3d031a15220c03060506040b0309160b0d021c1a040b03 56
    0x60004841541d484480d00c1e41200465168020312040104451241c418006403003000000389000c501810312080c15410220001c111724000da001c0e208100340349a103c500050f000c0100c0c04c001a101d5158614007040c5014400829017045c284018048540134000100c141920001040c00d0625118100900300d8890003954580c80280705003004001100704000b103070442550b0b08001c1d140d55841007101e08001e01110414000c510360002082901410954658001e01000c1441801c829140c0504541c10140b41d0045e86e41c0c15075a040c1e6400202c0307904581c05903410921100c802c010240c07451034070201c08c9074407004080c00341d202803085042440304074440d001e2a405030321128a0440410008020302040d0004054942100284607160b10b402440030340b40c0c0364802c07962441e0603840d282c98032901844104a641c2140c00030803141c1090010364801c031a0340240540d070b0300e0b43c898082035140c6000c842e41c0b0100f03240c000e00c1d50035441c4c420740840d04a20190703000d01404400c2ca0406441d1507400b4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 424855143 1250 424853893 424853911
    0x120c0715210e06090606030d0302032509081b01030c1e0509150408030918010305060c03070e060d0606090609030c0e1803031e0112030f180504020c0a0606050405 71
    0x81c22654100d400d0400c41480081c01403000540d88080541d480c0f621005440c4200c490b0048418401542000d01c030400040c1e003a401d09500d54180b4200c1280307403c800b80640c0700441c0c501c41d1084501c1380704a51071002007070450125441c00780c4010040030007070181c040ca18003083c9061a54007800b40a0520348c0000f8030000e21070b02a40d101c201c01034610f6402001c03819804074903141100d180c903000c1e42c050000350003540000c5444401d5103050040003c52154101030315055500100001080000c9569100e50641d40003a281e823500c11095666681910089030310460210f00440c0307074480e41d84524111170460340c0e18017500ea0346900688400c40355001c05040040000d00c00d00440041100d215080852081d604c540c0c1100c041c84241180c10503940000221000d2500781c03031034a00e40d00303000d01405091480400195603075a020308003201103611003083c4901c0700310000645010a06141c0100300c0034209543e02d42c1c0d01c606e01d64440b204841300b00ca183d0302c0c2c4440400c0b0f5040a12940380300351041c0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 424856393 1250 424855143 424855157
    0x1203060e0f07170907081005010e060a030c140d0b01060e090f0601050f1309090f0b090105160e01090513021b24131b0311030a080d0b12120c0715 64
    0x10f940700102500a0100106110340000080d460400300240d410840344040b0010345541010a040c046d100c001e4141031040340440070510200d282107000c48100c0340150b4034485640c0800700410354100d80030902900b401d5218000003201d907000283d03500344440c2120395500565407015006000748040c2d451314000f81c3c081c826075030140301c44002046464025001280525500c11134401919900102110b245c0140f100303100c2009840300710b284c0c000d0725200c024001c2e442c1100400c4c003540340c8410454204001e02003448a140d0241444602425024090700000c6001c2e261801c041d502c603001902c180003415040d81c000c014003043c3d9040c5110201914001494068034070604900050490014400160010700016000f81200c1c007502030850203c00740301c2e1845c00c014421400b0340d003480d4041c1e0003060380e80d40090421012a070302038090301c00020b01086200040340e100b003200c1e2140c5181d8442d600c001c0d8020f0030f041001c2c200e035482000c12110700c0340c1c0301c10012014005c50342501d0007058030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 424857643 1250 424856393 424856417
    0x50c151521060903090a0f050906011209050601080d020f1203070c031b1104050c090a05100309020d082814162307050d0b19091203060e0f07 62
    0x49007803896046002880c52803445101c807884541010001d030b403441029800090340c800103003018055900200700040ea154000e82c5003102044865400416481c10445688d4075020003900c6070b03020300384458110f0201c0b61150f07102c0c9001581d074840081d441d40035218614172131914510000e1205e059045e10420103041d031b00c0305041620724a1040c4012401d106641d159070b45051003410500c01c0850040c120002e10701c240c102440101d03100548070700081102040b074132090381c540d030140300c046038815a00340340c141e02190001c400502801400950101000120b03900b4486410b010703140240c00d0800c9007003004810038844589032490001440441c61f10b0302c82c2c4102031084c03c040c202107000000034011420f01c1d40d4880e4135480113202000740e0314410617131030801c40204121440c0a0724055955840e459095100c0c0c40e2000b01c002d0881911480b8600760048550141c0c00c044046503204151140c681c1400b807004e4040c1c0349a018516440382c0d02d40002c4d1000442c2c200c01402080d807a200c980744680 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 424858893 1250 424857643 424857649
    0x902041d0a033e3307080f1302010909110c010609020901080c03152806050c070509041a011d0718120c050306011502010b0303071e1b0303050c1515 65
    0x100f6a0018980075180b101441c064002c011540c2c0f04a2400815003840507500c42d1034015000641100300b041404010400d807440c1c124005030b080010101480c5042150f44012120204190481e691950030034408043d0018901c01826803000594001d202d003503201c40da008202e0107900300b4240041c1050001c1800a41068019500850342d0101411002c0d4400c0210345046d07035401298600304800304204c2c50320303c0300150017405041c05180040c60213003250380e441d07a40e201c81d005041c4611201ea020804001c8644e1302c0d0004039500140f00e03070086d07070741e40c0c49144141d040c07484c80300041800d4000201294411a80381407000050742892144174200503c94080c0d08032100110748001070705101003055501005024000c01135000210850691060000e0a5540c0509003a00030f41c030038007403140010440600c5015006240c00c0502c0d1000341d03070070599a00b9560840c240c4e04038030807000c084207050780400241907140c0420121003062201c944480c03400807040380c100e244841060b007621002d103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 424860143 1250 424858893 424858997
    0x3030b06160206070807021807030c0c050d12140a060321080f0403030b1e04060f050a061430072c01110708010c0215010605030106030902041d0a03 65
    0x20703014171100c0c3c2c24003003941d020076644003501a4452103070f001c410070009516814041c81e0541042c0e864018210701301c1e9030384d040e598030209078001c01740000900e42400b01909c40e440b983c815051800c4407500350a08214807030041c01d00d408165104050f51041021200070f40620a090814980d103029059070f503107848080c00f03100640110109901c030410064555960003e9004c10460075106040c1c11038400d0401c41150916030003140001c8690800304829581c0040c207a00b11904c60400b000d440c07102d075030705441c1841030a004401c540250010070a221060390010140900c28088031b420940390014142d600f00401070500d88280c0b011040309802c0c01d54010b07e506141410b0400a480320b80d0134003414207020b00c81d00460768981d9540c2030504059410004c00c11030040607030b07002b11554103000c002400c9200c140110310130301d034480c04e0407411512254401c281c103044007a54a00403585030700d0300588483c0d24007400e90015030f4981c00c1c40c0800c88101c3d0b0002800c1129032001c4488101c00366444810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 424861393 1250 424860143 424860157
    0x203120109231017070803121e01150801090504020d02040f060f0b07050d26100504050415110408070e180d21060609030b10170a03030b06160206 64
    0x600558802c0d8900b00e100510300d6400340494032529a142420007005599010f2a00110161035015500401c1041c20101c103d440d4101c40500201081d6608068030112415284480300c243c4554800000c092524146500d1805011b5980c03c0803a41d854110b102581c40658020f940300000100180061809500014854194002c04545143e17648113440c0225500e610040503200c00017840f44c20444107015203152106a03042048440040c03120b0000500c04501c2c1c7c1d00d901c0d851034000b0079540c2c0b055000444c003e03c0020700601440c54680f4000c407604005502c00520705040c10500c03400c04200f041560300340e44c105001054050300c0c0c40c5044030680c101070705445602d0401410740c00c3c1c0e241d00b0302c00c2e1140705c0140e80311181d00030000c1c041b140b00c000351103090040b1949000c405000c00d03a0b001a0310310450350001c4840d46580c131002c440e0940011395502020b40d6082d00580840740c0900401c64030071050003510100f1090402d001884210300c2a0060555440003103e500401803410700090425 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 424862643 1250 424861393 424861421
    0x21006030c1e0f0f0f0504091a090a230c09071d1201020d021e03060607080c030c0105090706110a050705060a021f0213080c032109031b0a060203120109 67
    0x100030360720f44455680303403025000f03c3e00b0560000d40a203c040c1c0d1095146005041c241c80401c5103550545504248507003d1081e010444807a10100741c208104212001201c3d400c011800d5454548041a21024803142c440007100c7c0039550300c5a0551a01d85203d512540090303d44580c5c201040406051842000029640c498074454450784103042c24800780450280c0b0301801030392a00005042c459003a1011a000807805040080041d43d0f1981010381d02080d40c0604419140e45890110700d05601404190404542c0b03004104401c2e03840000d540022540350380c80c0c40fa412003548906035254031000704090200e41c4440020405818114011708040f5520310640e0107030406003003500c41e00300707581c4d2000c0441500443e24146184513422000028042c4030020a001c11203a40030030b899074180950170060040d20b4854803628442c00702104d1403e803000b0b05903100c2445421000c070364100c12110513401001410404650607000000b102c0000300c45001c4002135030702e0180381c14054415100c0c0209 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 424863893 1250 424862643 424862699
    0x40f1b030507020a080319050f07020a03080703240302041a0604030b060303120f07020c06040608040b0415020406122f07050a080d0f0b060f0702061305090c0a021006030c 75
    0x800300d04050040e50003100c070034007030f01003003200803007d10b06580d070180035100c21104041c1031160940d00007800400c026410704104071a81c0d40c10100360028851342044010f01640500c5074000b100c0d40098800c1964421202008207a0a01000680c01d2483d480480e8210008020a01c04205e64010040d8401802801c6903d0003105440d685103000003554140e81000011090001072501400280403400702591020705091030038078001c0601d00f0290000d014500180c001c1801c2c0450f84500351840301c000d000641d5150f56516006080782180e11031700c0010340c60240f5001110b80c00000c51102e909035018030105104c5070060000ba19070215000b1192840742108260000d1405405007110920007540040e2817045060081d05031188110054402c410400220448003502003d403406150103544490302e03500c62810101d070703905894006d13981c0300340c28a04000016401c1c400401a020302a402d840d0090f0144a05101391901804018948603102109020000c0c1007000c4480c14801c03150300c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 424865143 1250 424863893 424863913
    0x9061d040b0d05030a11030307080f0a062d05090928060510060807090321120203010b0403031101020901170403020a1703010914060a03020f0105040306020d0209040f1b03050702 78
    0x5041001c2c5404200c80540011408000c115040421040c09446100155185251811000381058002048550b41c1220100070905507800e50f4000301c0a00000f03c02c90b260040030400101a12200990048112007003001c04a8641080c00500e40203071510720050810b1141c0b40c1c014414500d0000c00340355280d04d624041400309155004403400303003a4419508121a0410742c000b400100e0040001e000e2041c10481040001c0500380d08613040c9079844400c404000c011401160b003507540443c90420303c0e00110000c20075203485070007041200d100351204000c04d001011182c0c04d0340907026407540815510a40b45080c01460907646a0180c400d2056031255a280d99518010f5158100c806402ca800840140f111852501c11900b14002d08250344c001443d00b100040d40d00d030010f00000b802081000244009a4011000c1d00c0c0078650003081552200ca282444500031340200a03500d05c100d06101c1000713103c01092044554907000390308040440d150068040d005804040c11020840c03242c144d40c1c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 424866393 1250 424865143 424865149
    0x40c021603080306040f0209010c021207120b0a05070215070e0604120614132109080f01050a0c050918060f030f030c0124060f030f0f1b09061d040b 65
    0x16001462042200c070743c880c14007000380411505092065a40540f0402840207681c0c1c000210300c2d0190b904840944007145040340090414945a102c4050700500e07503000003c00c08034241d400d114070300300340c01002182d8484008aa40d5000b0741c10300b1200d50581d40110380034038410384241d156a60064401442e10745e0b904910300c1e14a4101394151203203981c0e94000b04120504402c141c2c0c000b054101c800040c80e040d80c8032144103e25030a1031240d00800c1c1aa40151140201c01540081ca4104151400402e400441c00e000c0e00342110380c10051403800e2104003004e03000d070007501c519200c09000107540301345008000b4160b200240c1030300ea0100384d014030249550303070030400c15450010750806903450b414075440180c2520f44003807002000302032003403180701d40c8403101085101b141c40c1490700c1403000b01d200c50b081d8001d00781400c85800090900301c100e005003140b9045044040090354003903510b182d03900d10884048486000d0762001580901c036201200031846540100242d000b0303c0010312120076000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 424867643 1250 424866393 424866433
    0x6180c18030c13020711040b0604170a08030103050703030807081e04060603060606050a03050609060d1b0f0f08240c091201090b1909030503040f1b0608100b0f0405040c02 75
    0x302c3d0341080c0c0015004c0c00f008200d12040c058000305817002d0010040000004030b00d4040c6014500140c000b4440d010003124003041119507280d0000103090b41e83d6105d05100307450b200c490106402140d104008141260300c205070300d0b40700365641d0781c208038500200c10720307401d58480140043d0f40d16a1200004000708100c1c1c441d000041c200d5403034096031030641c00009419a03a00070485449249500e00300842e039212042c00c96800795001c000c01100000b4641c0442c1c2c0307000300d9001040550700058000c0741c040100311003601a10b220314100c0b0001361110302c140d075440303102403a13292813000404046907440c030600c8050701e445000100580c105042c2c17030f20840d0856207a0002a1000d0440c40140f103140d042d100c00050002840650500c0074112940740940140b0010704024080c40000d96810300b408903e106400c180880345000d0008950b0b0385100500b0031109480080310040096400070f40d1800203000c8501100c0c40c03201181c00d0900d000b040000511840c5000002e6014040280140b041c05800c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 424868893 1250 424867643 424867669
    0x121507020c010f1110090c0b03010b1b06160f140315040e030304031b1e240b030709021809010f03110a050d17160b06180c18030c 57
    0x100030002860000300052000f2403c642040c14403503803201c039141c2420041100d40c81051030b6180412410454a00f00d40410003079880000100c60110012800400c11390060400c401090400078134248014151034441e28180c4a00844041001c2402d0400b40116001c0000b08001d042034680c25100c1f81900b03c255104580d42203040342403500b003112903e0144166100ca409910007981580b4043c0d41c042c100300003502031f0840603803510305450100900300703501000120b803061030358086074010302d451400c2c944220b0107210181c1b62107205602d085214400e001101c5401002001020700e001d100d103000707600810302aa0050080d01442005440303d0070054004c21298108100c04c0b071550420905220203d807443c0c2c482c0340f071102c0400c281da5402d103905440e01d81102100545070a4090415410320900d4540400107880d60201c009200725a0b0850340300e807034151030140740c940315140758031f0340880101c0340c03907201d58420302c408040004c515517604c4800e5400340c1150b500c507555034002204102074030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 424870143 1250 424868893 424868897
    0x90f060f032508011506030513120503061806010e0105070510110301180b060901051308010c0306030c0801060501020a0f06271101030608031b030405090c0909071d121507 75
    0x82e5102541c80112007141d401049904000c011600d00307401829402c0041c0d125410400d911071010550054820804460382c1f03038003071151191502d60719406409078100b10b8440b8403c420002c400d2401c0702103281c1035841101705a6139080c114000703100640d00da4100307040a50700b0380300d0034a50041081e001e20618400030f22a901880e04ca41c54a804100100a00c00c1c0050031142000c1e82102151501c505603013078070f802400c201c5d84076a4440c003640100e44440d80894003940c203103110381340040c2d010303030001050f680600351240000c1d44400000382071300d015200d2070740183d10a1400c81c0105a000c0d028802a6219030400304420030f410381c61035002415464031205011800610004105510780204100307a800c1c00c040c40101e19281c2c1503034032030040d40001080c440942ca0b203c6803000e003d0080b075000c0c01c0b00409030000c506260044002a810100400340507200040110300d0041c0600350203054082e0301c190171aa4120344205000c0c070910007030200111449500c40c0c038440b001800c08003511074a00d80d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 424871393 1250 424870143 424870183
    0xc0c05030a0201140a15171c03021902060618040206120108061501020d0c061d0303150103060e0c16021c1115070209241002070e15090f060f03 63
    0x213104d0003660501400300307860140b810790007a1110f0490b0714034108a0301c0410b0356070b4000401814031410090380034000e842240000c20444c00150301907015101a03100401205101860b078503060741d984c9401e40b0070070362080000d00079000c000495501e59902a1001d001c40d420003c50310f16000040500703070032101164001404025002c2c54840680144d64400d2005204607110f1031000303080003007030410151040351959101e00c02d4a0a18071403c44112640f812280d0724039002c0002c0b20102c2e02c4080c0d4034006401c0c103e0000782c2d031449480090240b02c10041780341c90140940787c002014080d54408903040000ea16881c0d0048a0300300c0c030212214007520004100c2e01342c80081203941c00c1c880d801c01c42108800c1c8450310250b1075501400b40c1c41b220030124a2851540010a840488041b0180704d42c030601c4401c0d141c1c0e03481e90216425003110304100d02d03505903481c2c44402400b001000c06141e41c00c20201800140c40460003501c01d600070f103000d041426040d0303107040442d0030401d40d68141c220303640c50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 424872643 1250 424871393 424871411
    0x201020406031505010c14160618090e03301302030f1f0f0b12030a0e03010605100f0c1704030b090d021c0203090310060e160e040c0c05030a0201 64
    0x243c0140b10100040c074090382c162504040003c1c295100d801c1015040c441c0b05941c0c02d012110403c800580180724071160b023292561220000c12501d9823003e03d0585201601c0009210741c0c0301c0c0151000320940402450030b201c5600508101c6000300c8060442d500b40c56036901c1040403d010620780103c60545e2a44540d0030a030041c9071034a2000392964015900c254403800300c460414482c441901728034400420f8140c3c1550308280a01440004141e10082509407103c8401d0000001d05030022180c60f03108100000c442010308940d032505c84c1c690440001c041040741203102c1d6214462800340c0e8244942c40040c1a113a82c112807156100b04120701c1c00008050050100194a40e03500103042c000404082181000094941c5484038404010029401451000c03500910907071394411000b83c2103840180895110a010704158418002190350a801050703031054000a007101d604550707160034400b048d05070240b20045c81d1120140081005140c482c8001031018001006c8205099001084842c0c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 424873893 1250 424872643 424872647
    0x10f0501110706050301051203090303040e070f022418060702010617060402060d0b15072d210309060905240115050a030b04090b040b010501050a020c131503030201020406 75
    0x720301c0d9454002a4003044040080d59844005c482c10f40d001a115110f480030213800701c5103103008030882540d040c0004200031518941e100f11883c0300380b50654810010b900c034003001341e032643c2c101590b00ca103011041c0c0c1c1c2c01450701440301c2c04503006500240d81c41681e84d20010520300b4500162800380c0185d468050070040f512744903c40440d03600e580f0024000c2e5041680c00260540f003500c1d21400c00070703103e1403040341540d650107035450031521810410ba510b50183c03502d0b8090042c4501040700c11001030b40880206891401d242c0b0341c0d076501c05420b90500c5181e0382140419001c02090b04101b5440d03c0e101d0700041c0300d0703015294005100d0360003000d507500b001d04c20516040420b5948100d410718400100710135a034031552024480c800d401c200d82d0782d0603d00f5049000d0103020404580180c28900301300c0030411480001807003035002e101211480d9072214011103042c82161612401039100320b8103074403640740188682c010395000800000d44500044031701054201d482d4401e9000d80d6012908110701a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 424875143 1250 424873893 424873907
    0x4031704031b0602012004180b030619151503090203010e030c0f0106060302130e070504260105070206090705120a05120a030b0418080a0e0406140102011107020135010f0501 76
    0x31807286c416115820740b00065205400340303101c0d5410131150611000c0603158594450300f11030340081d043d96450310f0512040d28000045180c09001c15103880000b1443c18017110b0a039050b12070b010426440001c050390210060141540166455503a4038104012400204002c2240038160ba000d407200160200c001801c4405a40c1f005e01410f00422542c0900300308624000161485c210701e0110513202e091003100c460003a60420340084444980d1741c1c00401600c94282c032401102402404260b445810803a15401d00b80c90004070f980c0100014041071501104007685540b2060407076402280b6512400e10b41104050460b141c6040022200086541802407007070000c2c054900388110303c1401e00d100c140c201207042c0034152101c00305d03685542074030981ca400c0441100600a101a9407100c40341c141000140c1d0a541c0558a411040b810600816059400c031a805071252542c0f1a860340380c0c04e00e50004175070b00400a100d4140c15031492a002108940a4030030300229204407403d00001601c03031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 424876393 1250 424875143 424875161
    0x8010902130603032f060a060939020a06020d0b19060c0b07031b02071805011409041a041a06121b01020c061204030e06030c04031704031b060201 64
    0x220b0034010180080382e0032952620502c0c80d10044284426400c00114400007844c0040b00c0d2180698020b0040c20700c03580d00300034150787c83c0e4a1300704424081c1014810103103d50120b03903688040c03142d044090640e840c03990902c1400301c0c0d006a803a07a0080e5030310310781264000007681400b29030707036040012542014040005030300d05520001403254240740024215940c014002009142d001d8000342d8220b00c66080b100c5410505030f00410b410380e0030306020352038822030301030706a1031401041d001c4041603240c0a580d040710101f0103c524181e4501051000d1240014401d8890074078690100094016118865202e207018000303402d011705040d9100600640b001e050f40b0b1046d005e800382c040a543c0e001c506001c0901ca503100080c40c403561800145c2c20040d04083d015401000815500c5c412440c403d00e25114601c02d42e124001e5640d240e00b00f229501064620040055041c44113000141141042070101a40c1440170340c200756070395a0f1100302e8107199040b6220f0f0880a0002c0014075024010f09070301e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 424877643 1250 424876393 424876429
    0x190b01051c0b010c080d050405010f020a0e040203060f060c01060e070f080a0902030705040606110d0314070819020408010c0206070504050114091f050a020705030105010e01050f041508010902 84
    0x41e141007030284680c03510442400e150001e0b581c010320b06441e070041402800c02507208400715150072883c00004003c02c8202c07425291942444010b00c0940c00e60300c01c58070001c905440f05800040514180002034000520351034200240c2d90f0100c207940d4a00c3d01034003426540394004269941800100d0301280c0c2c0281c0a4001d0040b445c00381d90240e900a640030340d00058044002480c542c84d800020b2510348180d0007a504a40b5000c800304071541d014580c4508098100211010301400031000c5088070040d11a01c50b00780b002c1d0f804641c2c0b0310b00c070724240d641019460001010404042c61b08108176405507002204681d5070310040e118168043c002c0715813081e0141886030034607203810300103070840740104c1c0c0328902d603540040c3c1c20705541c0d079030407800c0d0700078010f07058422620320f0720340011301507a00000c120b002510031200c0c00912450305004841c161071a2200740e0704540d02e4081844510300d10700c418a0750050f10364801650301d01e0b0f0b200d10400242003401c00850350071503a005002424803c917000c111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 424878893 1250 424877643 424877647
    0x5060309031309110313051203091b0d02090f070c1703090d03090b0a0b0d21111615030b280909020a2c130201080c03070207060e06040806190b0105 65
    0x407200c001c0d100f546d511016102007480c2c80040391410f0741c03c00c41c81001c3d05074820808418804c0200001513480075550015100041004401042060f650314514000394040454800140c05112141daa0f68110405041000040040c0c2d51292154462141350f031000c10000710422101d6881004143c0700c08510f800c0400414440b5120545884002000f0383d84541d200c4501a8081d100c0d40ca81160154106103080d0a1140c03803086903412115071140b001c002010081600400007002c96140001c1e02c490400d030180500d0085002d02c410426002d540500d0303529182c1005a031204041034109403842807501c1044c450340c072a406082c0c0116000900e24918205100c4010381354100740c0c0041d500a00040c00c9442d02200880c1c4040c02c0724a402c40c401c070702035028080009208031440001d107100342c0303580d4810340d1016880301c02d0b07000482c4c0f1840143d05c8030604010792801150030f4011030001804861605455410f05843c216068420450007402d5030300960b121131041c42442a114403d10303203d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 424880143 1250 424878893 424878911
    0xa08180a0602030705091206010807330e100305060111010903050906070c08070315050a0515091803040e1e0c0a2a0b0a06060e0d03080a0605060309031309 68
    0x5035645440e803100a0501d94000041809a40110182c1e00e000364010302c02840104150400b6464540a11810403e0b201301c44000c20040340382c150002e996101d4241c1162a10810701482c042e204000241805000c050401d4500c0c1d521442e504031000031407a10042580e082c13a02c001083c03294204800c204507450600310400281c6e00c20100d40040004845541d285d80303150a0122441b0b85d1944284018421940004200000500386041c07002d5110820043c545d10003000700c054810031661100316403000a1484150b20b89000e44076040405210f110750001041c01070a071859001c0d410034011700c039080040161075180040b080840000c14006040541407035045040940298507055062003010300005c118841c0c1e2020200884081c0f0048070040e0642e41404428a03800f519079406850402c034004c80c005001d40103205407404007a2202076101126202252043d002501f07034aa102d486840c00501c0e0750794840554004d1030048055079031080443c01c94040c642c403591022140350f040800c05 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 424881393 1250 424880143 424880191
    0x30916080d0513090204030f0b010506070b0613090b01121506031a040503070602070b0609060a08100b030c0301111c0e03030a18060f0b040606030e120c150c0a08 71
    0x712240000303091440d142c090840d1407110b40ca18a4002c00122440803800006104410710314448450040640f580303141d0f03c60341808483c2c030410070081c02c0c008411021650750300300609000cad491403c071000040ca5501550703030300e0318203c0b0a0380284c4a0307051803440030090048000d0348110868801c0404c00c00b56240d40c0d1800000b00045000c1c000780b43c10100008e0902c0400d01c212400180c0c01142155030790210710f401c03611002c081d200c40d0f0040d015000010b00c2070406032810000c2c0d0b0103031b100600310b407560042c0500141c83c1c0c86a01c0c43d0940101c10083c01c05403070034003441000f1200342d0a0280c88213260201c840409a94481d01ca2501e41880000200c1c1c1c2008403c5070b401a10710705000c0b44603007010000343c0d161480702c031000740128074021222040b51004d41c0f00101c0714404840c148802035984030704034180d4100096130100c035006598003604000c6400c000302000e52400050720b02c84100e0040c10380c0e5880f2704940c1c4118840d000182240400c0d8000c03031080e030145a9001810084030111701c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 424882643 1250 424881393 424881403
    0x1a03060906100507050a080d1805070504020945010e040f081c0509010f090218060a030f060b031e0a0330140901020a05160201050904050a0203091608 66
    0x1281d004401000b0051002031042e4101c43c4100c3d0044105d031140702070f61401c0d039000da12480107178902c1843d0010440484608174491030007180c02000034807105040004000081d488283d40713075880303011000c908610803902d044003600e200880400c0060308040004071803c6605008484400600f840014031000c01407500c0b107500550040c285148000c0613203405080b52050180440420600b0783c400c0340000c0300c6400040c8203201802c002d101040303c013620041580c680500003544001c6545031020340044030760358035500c40001044458202c0d900d40340c607102c50840090a0355803d03282c0740c0e001c105003800c0000100c0640c0c100105000c402003081c281352a104003250050422800b0b020f40d6581203c00c4400001c01390070b8603013200c1c00010710300b0110020b102c1c21a824038002000c3c8001801d101040c407d8841b031400c152a213034a420403211030741c1f01000c040041241445814807582e01161681e208041c45a50a4080160b4038208510790340d14120030000000042110303c02d00340602580491 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 424883893 1250 424882643 424882651
    0x9061d070e0612010905090c031c050f091804110f0609040b0a0f14090906010e0403050d090b0c031509091c03060b0c070f060503160827071a030609 65
    0x151031000e00310074000155042c40782250208003500d20b4070001c00c10042c3ca521040c060005203003110800030421040c140c03510820440c511401041c1010a00f01a0064000f81480f000041f049880c00d24014001404000a81c40358000800e5000401041086c00c0494004540048604001c00302c029030000d50507110392000140620345820420b08651988100100038180c0002807610141c3c0f01c0000640d06000c0341c00051040038034902050402c0004549a41aa1500c1089a0290b510f50b102507a860b804074041c00001c80d50340c45060301144258103118013032104225a0340d41d0381868980300c10000c9403c003085104409100c14070041d40320005242000409031406000c0b00403a081050700207242030f9200c103d9003a40080c00a401000c0400c035071050700c007411800342c245070700d40f44215039902003250340c60303051202031044110803801084959804081c2d180d8064100c0518034580e9441403000c0e41e021038580c0913281c1071001e83c01c000c1c4112080400080c401d41503191550001303580e07500141c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 424885143 1250 424883893 424883897
    0x7031101022b0e01031404150f090c0e04020a0e0c0415020c0a05040b060d0e010209120601031101030914030703020a0209220b1e070c030e0a0524041802030109061d07 73
    0x3180b0183c0c0c3d001340c0107001d80c2e0074120030f103840501e0142080e01403442e00b4400405018601341e2080a10809841a00100d40c2c10805848000703081c840382c40354441015001781c0c1d02ca9000f15001511564007c03480340702d0810b0000450b121454001840c0c18107400c3d61880f0255044400c1440058440101c201c040301c400300c0300400c600300c880c001300318a48039a281d6140001d04200714590f0070001500188003404d42a680e0108151000c09900c1d210082030100130450078003910f07823001d03e600c40c2d000154500c0c09020400c020320881c0c5411071440d8014201103015030442c0800300d0543c9020385c03038035034804004203203a1000e00d04c0b87d2100f032740f8a15080c401170125011901069081c01e00113010b81500c2e00710941b1108a0804001c09005000310010450000c0d03510143c9841c02e04080915404031000989000006006c1c04400c0b10342e140e50640c20903608000703220000d00f58003103c8440c00d104c0c200100041c0d480d41000201002c3d100217400252041403484040140c007106072207110b85c000814 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 424886393 1250 424885143 424885157
    0xc09090a020409060807051201020a17060a0905010e191503080708040e0c070b06030a080a11120a0f020f03071106131206060608090d0f0e1207031101022b 68
    0x1500300e00002e00a94000420f03003032030a02e000c600d4400000700b400985504642005c0c0012101d030580307080c0e108a03000400001e014401540ea01406034803039a400440051001c540251510080000c076407003603001d0300034110000e061000000b00e0741e0010207000c07918034080c00f901c0b071101c050410750042444003c100070340c0001d00d101401680310a83e005028040350004190505a40c03903503803a0041300c000e8594000100100d00d861500240e40c0e400ca40e4000105401d0140f002404d43d08607840302e13243c459034042c0303c003103900d00c2c40740c08002c00350400b10ba103408030340c0584030100a29050102c014034a1b2a0301c200b0007000400c1041d0280f00804500700e81c2c09a4031402c840010300c13060ba00740e02070a100011095001c4c108074a030780181094030f10966507007107251303500210a07548003151094000402e9010804008a5125603090036800101614842200048400702803909050303910a03248403003654a01078140d030f8103024140d03035003a0a905441201c1035441c00003c1c0030b402a04404240444 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 424887643 1250 424886393 424886401
    0x115120f0c0207150c0507091d070905070e03060103020f040207031106010914070f12020903010902120601060201110a021b0d05030a0c030813050307020607020402070803010f050a0506030c0909 85
    0x145400c46055092005014448000c400c00702a6807030b01d540c0200a4005070000d00c640c4100d1054200c802d01c00c2d00240108034540c44c000d00d110003485e2608904c071044428401d1041da403d8104014002803000703160002c0d076443e22480007818041c4070100a4801d4010b00010005a51408024480084101e8005940d00b282d8542a40d000d9040366030908a8043c1c00c0000400d050540d0140c510380c40d51036204513440d900c9000840f941403022601a001c12201c1e40b01d844103440c1c0e64054407100e41c0140c000221042da50300010071003c0c02001c025600d0303000b0b40040c00215420300030201075603080b031310083c2001042400603485010500d8100c1081c0d07400010f0541030381d140450750364400d4025003641e0303840f4000080140103601e0840c0a034040b48161000c174240c07c000514264500c4d42100145041540590802c03c40ea44003d07800e030f9000e50280702c000d01151480c2c000710300802a06403c241c8082c41d00c01405110310003a408544070394400d0040290344403140084590240003280c205034169a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 424888893 1250 424887643 424887677
    0x90e010b030f07031a09030d0f0b030a0c05510f1e0406140d110301150305010509040f0f0c0b0a020c0f0d0f0b0403120f050105090f0115 60
    0x25055038425854800d80102c5490302c0c00200d103150507640640801c0e1101200c2c82605030600c1c005031200040d56100f0040070b007142240e5400700c0000641d0705408983c120440c00007910f850029042030300d008142c00310410461500415081c502903850001c409c0c0205020880004200b0101e44000f245103140f4a0002815180d515660581c0344410115101d406807010311803950042c4000011682ca00113003251441c540d4800d5032b040b42c1712a501c61042c034410960301a1135400050410102c01d4540b10801060f009103005503010f00a007030181d03901005182401019250184c1c0440e0142e9584000d100105101c40c2c0b01d07440d0b00c0c0e000001c1240c0844580342a000800569200c82400c0310045000002240c1c0403c03244a00c5801b1207074000c1940300e10007040001c0201c8a00281540451000c000024010703210346903005019041c01c0c0700d001444514201500d10301c030201d907a03880d40d8000502170f510308002e00c0c40e0082a260503d0400b581400c003903641d40c0e46004064010b001c5046084c0400c80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 424890143 1250 424888893 424888901
    0xa0816121502030f0415140c071a0106020a050616080a0207080915030106031a03061515160b0f09060402010828050402030d0c050607051305100c060b04021201090e01 73
    0x105a20115a0f9140c4003c90805642055904844450902541090611a5019100c44904564024051529114613001041d4003440c0221040c2502031124107182007070400140c001c0c1590380107407280700a1446c20760704160700149500340305502c0c5000c60002c3d66010748000d501024200340180e0fa003145040654039030241e400075980c07044140c08142503103180400518102ea18586040c007160740e01c110911140004074074019010307440300c030014601001c65455580c44400103061100c0c0041c82c0b10031078003e50300504494000f4511620050100301041e08000e80c40303602040c4a041030b0401d400603940300c210103400a810482d0344070209d013489800a2041000c10302d05000d0101c01207281000601600e41228261b11a0284000c1c800c1e00c0c600070070711180c1003684103020300026a20000156820380101441420144008201052a80305da0340340d08000c00198803480301c0e080c050301d4000d003500d0101c0340c858012030050051a04c0e04683c41080c0741901c200382d4010904506001d1900c1c010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 424891393 1250 424890143 424890173
    0x509030607090e070905010806130b0d0f050c0604060e0405060103023912040e090709020a1101150b07110409060c0f171302090402032a0a081612 64
    0x500852051100341600154400d084a100e010b10248503a6801803e031640c0385d19104880c00300301c030840016147e24041d403030b6a0301d42080b01c8001030844405030110b9000b140f00e03402141d1083c000c003024400d002c410040d181300c8400444129140a041490060401e40c071030304214040c035244c00100c0e043c1e038000d8042c1c446458105000044010681d80703421080541000c3c01c1846450981c45241716040c081508d600c09550011010b1901d13140c50b00420080360001c0850440740079180c00429a0055030000f00700704091682c1e0b0802e0501e030702802c1401c4880d1038034074540304e222002081186c0094403003690140ca400002c52401104034801190140095650003803200e846c01503008501c0b500500c52004000443d500c1c04d8946940103100c030065102a02c0509807142e80940b40c1c1c0061030011200366019202906a443c200165820382c554280c01900c204042c1d024040c4540190820301c1400c001095200014120106291090f94008515024542488007105003110502c4040002c8901c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 424892643 1250 424891393 424891399
    0x10b0a0b0c011e02040e06040b01170403020c0303030f07110607120f0e0d05071b050319031e0239040b1503010303080a0f1a01120e01060b0d29040c0509 67
    0x21100c508096000294402d00501d4506c12090001c0303800303402c051003507040c1041d0607111112101361076a001c031620440108204c0462140203800e4215480c24405540201065803840c034150516040180c40304003100c981044a600c01010800c60300d03030004810300a441c858000183c240b4226000401804d6810000e80c0d080c45055100513145901000410100d402649080d85540d1046004114101c0c207210312503055009100c2000400955403003035002e1440390a041d010210322600c20342c440c45200c02c040340503802c44081600d0001409002e031141018030103d03180781e022541901d0b5440d1039810b9444d400381ea80c45041407150340703e6803800e0032860030783c0c0e0b0074035165a900d2800900b5288120b0703a00e0009400d000c0001103212150044245100c030320148024545160801128800048410804099144e0108640703840003840703100c01616081c031490340e48882e0300c000881580c00300500c81102c40001a0540c1d0344142c02c3c1c1c0344102d00303002101c003c10a8666400b0484143c06035203001c0358 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 424893893 1250 424892643 424892681
    0x90e06041b03021c0311030a0c290f070306120206040e1005090108060603160b3901021207020312162a11060310050f0d0602070b04050c03010b0a0b0c01 67
    0x4813100ea04400d200c00544240d035020104040c10700c8803a20b0380116003150000c00c221014800c00210124002c0d0700000c500e82d041d800e11520b5180082c21080266101c0307001e00400d40c1400030710b5038140101c4001d080c002d840704130751064903404280144500cac030403041440b8402011902200c810310a4400030040144001480c2d61030340426610340c0d1098504902c00e215400d4100b85001841c0d00d00d804a031401002a420b00c1101424030a40701c030040021140d2081c80440f84001c11600011002140e1000000603228a204500c250f48074002038000310556105200000f00308030215402c1c0d91001c00340d00500d03400050788000f911005000c86070468050000c080741c0c48014500100440391a009403100c002841014050204910007512525140032120905201074102608402c0c02c0070381c05800000f400c146600e400080340c01420302282d62203098801e11090080030403482c0000c107421002046290304140002c4d600240b41e100f50228000081551030280e40e0a51184001640003040c3c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 424895143 1250 424893893 424893919
    0x2040e012d0b0a0308180d0606061112180d06090609030c0209060414010b09120114010302090f07090e18010603030503010504150e06010e0a0b130f090e06041b0302 72
    0x712800245075020341d1035882d1610342000c61404961a0040743c1c3c010007614500340e9070490b0030412045000390650130501100c00c05001440505c603a000604042d03640680f505028505c190078440b41d031031104e0200300c0c107105c217800300c14020088044a1801321400000481d1034500340001d40840d000107060b480c9042d0080c2c06042c0c008582d52255403007200d00c10031a588034410401201d4401114103888003000005100b01c200c507900503e02c0e241c00810b1418500c046655440c00d448074100011407400c8580300410450910b440210b4004111000d403141a01d42604010208413543c441c1c107010360344030408190790140042510421f848a50000c0c008152039080c090480d510a11410703010390b01d440c0004610322401e8004805843d00c500180c0941e071581c00045403a0100d14001645c002c21150300021000381040c001c001401c5400c204440451810004140644481c0e1012401906040d6a50170103280031075100c3d4041e80c403070104000d400400302e2011411190303820094014424240364 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 424896393 1250 424895143 424895201
    0x15050402030a290c2a070b03010308090108010b040b030403050706270201020f3f0a11010b1f110f010c0c050715090b031504020304260f0702040e01 65
    0x1200c0c101000f60058409464842d400c101a2040b4a0910059141504e28081c90801d068900c501d140078a1300329091a910303032a003108554801e80c422a04140009418001075810855540c0100040e2030b42c582000d180c401c42180342d1200034001002c0000004000003084456404802610380c032a40d1944060203840d02c0d1000444500800e038007502c21500303590301d0102c2c002400c018082001424892501c40581e54502e052095200350003134a0036035030414003500100000d06214007c699508003848104800503084401000188d07000303502c17120f0240800f15440c0c0c410f100042c841e281a030081c00c0e0380c3c1400c50501c650090340003a0340d401c0803d40c45500307901c501c038101c0c40b9010700281c0320450354410100c0d00d1a60b200303c0c42d101042202c1c80c200076460003140507503400311102180140ac5000800090201c0c0d104950495040c48420040052000c0d90315004100c00095121581b03843c1c86220882e8050007840740080c0f007942c45120403146641d0a40007400c08148852004440468075208 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 424897643 1250 424896393 424896443
    0x103180b0603010501090203060f0607060e0307030c0308090d140d14090d030605061201060c03020109020907080f0f011a0c0309130519090209040807111002030d0e03040315050402030a 81
    0x80103110f90300b40f50001c42c2440541c0f0071039006000043c030305040c42c00004103100700c6410401c41038032415900c034085a0400d4060004041d164800c0d506c9207078088031460701602c1401c0181c8003141c1a4004003c02c1e0019400c030189501c4089110012522405543c60200141001e40842000d035444002404550703000000c8401140105072414000942c840701401518003071f00310a0010000300c00010440c89002d0040080c00c10300030f100124590a1907004201064016120715000404900c200100c05559688680d0400c969035400007995143c582021a81d543d45402210300d0072000035500a003110400480303d140c0c1005c0c00345800c45052803040d1004050803141001010620840c44550356a40c0c03203040011580188010b0f481c0e02c503030326100038a80040c4d600b11104c80351080d440d6582ea0307400401c0f90054041c0d500955940f180c0311ba481c801e807071200c03621443d030350b009010a000103110750b1400c1a0b0030b00c0c68100006e941d6607600020f4901101d511016000c502d025984501c400c9801003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 424898893 1250 424897643 424897651
    0x411030a0605030c0f0613081b090f070c11030307060e0c0102160b18060d2406030b031002031f0914280506130f1a060c030301140103180b 61
    0x404120781c6580d8424181c5903402210003550001c0d01c001c0c22450b61074902d026150840ca41000001e819480ba4143d510b014541d450410071410300544035041441c01940d01d42d40a51490268009414200e00203040101c0c1c1c0c100007480100001011103c50b14204280d0356100d4000034140902d041c0c9c1c00c5103a0f00d80903200509801801049961202d19905c40010300c21202003058161901619800209c46c2420440041e544003404015600f007103103141c000e00c140d801d01c0e45101b58401805800ca02c0203194194032001c20315080000844803964040360500214010300070240c1c0d81d50341c403110100744a13452440000c3c000c001d00c5000c00c10180a0340001030014040c0309004442e11140c800d68090541c40c01451820400352407d034030f81e40d8046e0059500408050300103d1500c0441c054942602d03907543c07030f032a940366441100703440c2e004c0c40c2c98204401c40c000f0b0b1003a6151482100b0b03c0d507200e20050240c04010660300b4224621a440b80d4080c1b4001c0d1001e01407034212203241d107041402154169 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 424900143 1250 424898893 424898911
    0x9030327010306150e01020703120e010909051b070c03060e0d08010911030c0705010b031b090c0a0f080709270506032b03140103050601060207060c11010309050c041103 74
    0xd03051040d50081c4a1102541c5001e1480b02014a5103a411070340300000002460440c002c5141c000005002a03643d0803400d01552654004042c000f00010107622603030740030f180c00d1030030101405030045c0c4039203034802c0500d44c4600466644540b8104103007100d0b03065100415251405006000c0c0e0b005c041364400a0b10344076912903556903030783c2840f402560180ca008d004072070401c0000c0717059000a14020030b0340901c218008180315101d00700081c02d0100b04003454a520fa4142c2005000740762480c6100d84c440258801c00b42408180b0000800e00b04001d0880b0701441404000300301480d000c1e2803201e0080ca1036400380c160300103802d8640301200c41d509859181450600e0b001c039515240115040302680680f200c2c1c20444031440740803568401c94860b40d201803554482c01c415000c001890b803240a180100000c181e99450200c0083c40c1140c6a8000020418245201400513001e09007001000f0f00919000c107101410342001e505018508211a5110b8a09800f16520b02c00100183d172143ca080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 424901393 1250 424900143 424900207
    0x3020717070b1f0506032a0901200304060503130f050109030f020118060507050c10090c0605072604170c0a080705010c150b1302041809080a0c08090303 67
    0x40d800d182002041d02e07a903900501ca00080520045c24a00051355100b0842940b4a8444000c0b038020720b400d6812030014100e00c20001a54240c40d41c00c02c001003100086003410301c00d1070b100ea90850f42c49001c0c038000c60081000000c0400d400d038080e019400d01460300705820702e0f0303086018074206000b0b00054008801191110034200700050042c0b180d0031081c3d001c03a99000070240160780300002010000c1460341800401c0c0300c00d003081e03a0100038580102e404c40c1c1001402130740c0350911055451840d07126030f0030080c0421003000051500e144800000d4002c840401c2040c0c41360191822070b002d0740d00040d01245608100343c421200014210701d4200d402d0701d1040c0311b02d840e0007003a5122507440c0a0301780418a400608000140138210480310304444980009480903020005a11110009410391f11540c01140511903028001c0d000d000b50702c001c902c1001003101070f0f5a8000d45014030300d8641c4c140106001d4840500081204680c0042e60090940e076503480301d202c40c18584400241410040081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 424902643 1250 424901393 424901401
    0x120a0b06100219060213080f060c0319020a0201090215091f0c080c190308010608060a261002040b0c0f0d092c15013b0103020717070b 59
    0x44109100c1408846501400c1051075a410320010300c00380b40f0301264450303400c101e00c02043c002072000308003034802d0001812846c40541c2506141000240031321319441010414441507440c0090b0303a40c44010b020f0000b68840ba00d540d0141d00404000d400a5007200d001c3d410390403000c520f04002d00440328111024800d86d060001c40c014080e4501d44c8400210724034400c0000482c406c0b10141c8500c00c5400112074005241140d954075104454404a001c84c0c1181c0c0144101a0000480c03903215105a4a40c00001e10305040c14141602540b40007480c80300401d4940c225a0040c4040442a10b0940080d940e40796503121881c1c00f07900c4101000e0880c0121908400510070119480450075503941d0749503405420065a05642500f0031101400d0800760780c036521000380d075038503414880d031407200d40d0300000d04c50700c000581101c1840160741e020a02e05142c13130800c00d082120a2801084600b400381c004092280164000d11070400d024008240c01d4101c9642c0c05440c00003401049c0c85403502180301c0e02c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 424903893 1250 424902643 424902649
    0x60f0c030e0c010e010c08071e12080f01061d090c130509011202190306050736060302030a06120c06020c06161e060c03050103030915120506010e120a0b06 68
    0x290300c0e0b1a10380012200c1000780b04541c89503c202d84018020405075140141603a502d03002c07480c4a868090701d001403c0e90703010034014105a040e02d00c0d502410652440e2620359200030344400d0500850701030000794206152244030b102d054240f07228015081c454141095240c112085d0030601d2242d0703030054011008640c60502c122040d04031004511070420500841c0d0070045030f0b880071280385600b0b408621000002c00c00c603024407800340081e5150341c206108009035041e6440b89100110000300d10b80300300540b049400e1484034045412030300e401a10b81d120350905401504a9a0000c00a868900710b010148416105403330100c503040c0d0221899110004184003a42c00f40c94005044070600007048000301e03186424101001d00c0f101a01540562190364103003c0700c00f483e004000081d9210018801c040c0c10604500c098450202c040039000740c441c400421290b903901145039607645a0f80458030343d9001d0020711000380c0005000b000300e0800c503c20a5528101142c003515501850004154541 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 424905143 1250 424903893 424903903
    0x9072604051b090a020c0307020d08070203100c0e09100b0417060108280213020c0a03111207020d1a0c0a030c0906050909070905100203180a080d110703060f0c030e 72
    0x2c0c003070800d40d03440d6130304403d070302c000c0d0012140183c96000c10010200160b407402e1111074000d00c264031990b20350301c990041c9481c0486403428480b00c00d1400c80707211240c58101803040b01b2504225450031035030340c40f4050211403d01d540d1202110703400200e4003150030a2900d20790ba80d48120001240d1840c0e9036401c902d50f640400b03180000c041060544410480112044c1303c101c80350024002d0a0320301c00042740d02049a0052940d03640503004050340781e0425612200b501c0301160590014400c1c1c07e0b890100742e2207803040035002885020410211400c020101d0800903060101101400807880e01c107802e072895a00c0144400c00084c0742c554100352142c02070010b01c0588015a94080c145901c038001d00c00c0e881d0000d0100000d102c590fa10000319682c0d640018800700140d0b902440e25030740c0900c00310340e5014850568601c0340420b00e1080c03140c01400903410b6410101890011090004800b5490429005800c0a1b046030304148800040c6029504281c0ca80800c6030f504009406c4030440883d110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 424906393 1250 424905143 424905193
    0x15030e010c09030803040302031c020919050a0504020901020c09040609050712170f13080106180e030306040903051306020c0f030a1a0c0d020d0f051003050307020907260405 76
    0x1003950460180b02140701304026545c032503c6801280d140200010f142070b0503903651254610f0054000504e40c80600b0305081031901c00c00300f00380c10180c25040c40c0004500d56440e0107080c0c02164045080e410305c0e0b01c200125940d8800182601c8680d041504080000e040c403918241c0f40382c80303082c90005000c0c5e90303002403006140d001501c08070070014542141075664082840041e1203607081c499580c1c1701c2c0044294400504045000051051800c1810311888009150100a251800000b0803810074080708032a813240d011940065201008c3c68155500e02403102c4040c07034800b911801280083c4c0000d01c0502c00201190011805103c020405640d071000000040c40003074180383c01340d5000765011025402c0170320740c0e100d1030a1140d82601c010898104945482c401c6842d400d46001803212f40c0300e8039070040d021703900c948103c80c1540c84071980da10596000030301810a01002403c024494481000620740161002ca002c150180100558490940d02034a090190807444c81104800101c08600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 424907643 1250 424906393 424906397
    0xb120f070c020d020103090b0a05040b01080115090b030a1b090b04020304120c03050c0f15010506040806040f020d0b01030809030f0d17180312010303030b060f12180715030e010c 78
    0x404840d0b9070034005490302d1254124141629413029030005105c4290b070f1380c0b04580100002840d0301d4107040a40d01c807503060340700d007846902d4076044201d0001300303003829070540321200d078003081201ca043c01285c5401c0e40807201500502100071032141140180c0114411280c80748001e011101d54030301044224030058500804000c0f051064460207400381d41da00300558080e003405806c280d43e60548a09110042c002a8600c1e040030042402c00c426159a03940501b02c00e0716103906103400d204025968240c0a000900a80074803003903c01190703128090080d50591000d0001c580356900c0c030b40200b031038002841e4141f09004402082070509000103040b41000020359400010041069844042e40303005003a288840400100c00340c2c2a6000300b0042607a14100e082017040d940c551b00300182110286010180b140b801001852100300300c00060f100070703d01c140084105500c650320108250450421160034a0080c100002141408200e2990719984e180d20240701e00414103607401e003225540504840 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 424908893 1250 424907643 424907657
    0x5130510120c0c080a020c010908060103081c0f0911031005150112020f03010f0501080a060312111504030513170303150a1a030105011106060906041e02040b120f07 72
    0x481d0515604950404505410030450000315900d402059500200409025a1040070350701074a5a20100400c01490504061700003941599524040740c0300360503d045071413200d04141001e4401d194000d240c606081c0d1010820380381c00786080c1c0c1410200300c1d0070501c640500c040c101c1450000b4003070188128114040342d480380301c0110040d195402c982d26a201c005500303005041d96003462400450190610080c40d098141c0781800042000e02d0042607008074a040402c2000010f88400c1c842d4101c080b00d00b040d07010500d90341c0705a40382c42440542a09c40007504010710081c103800c0030080060154042c08540345986400310000c0d080b84c42c200300c1c212a4010800500e4512211158848401d0b0050164545940d07aa0ac228003490014949511340440040104450340c0c004406054000541020b41103615054000401e0113000600b854041c58460301004443e910305004074001c000140421034427903465906800c0e46400c00294034201c01070b1340e0302080c440b810000e5418800c41450792008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 424910143 1250 424908893 424908917
    0x706020d0e240f040308030109060509070203070c090b010e040c0801050103230c0a05120103050d0e0405060d170f0c061e01082e05090a0605160e0121050705130510 72
    0xd501c81d0f10000d0640840c0406200100000382c1c1c0000850081c5007100020480a0801c0100484c074040542154150360003041400005590a522031046032404800050a1b610000c0144c7c2c000c0a11400c1d19440b03440e1100100c009a0402d280c14142e032000c0e6400c001c00071885000100721040042c5015210100c80001004c074010b8000400c145141d07841d25a09010000311030106084003a04100d8003500b0060300b8407816603200d42c903a0b5544a040358140700b6420a8008903407484420b032005028090000d1801e400c002c918422103d9611031002c01ca99103400203400291501010344455640b0200c051115200c595096141410781c0c140c803028112542c0c142c00042c0c000b1000040242e21259038903003aa030380d015644580d0f0b104450300c9000e07000070b406e1482c00e0000c8440043c281c1c26201c01c9104c0602d031640d845490040f18201c00e007804202e40b01c0006800b080099449800c000c224200320030010b01c03035800710140c40e4080001200c40c52240d224010809000710303e428043c00202001254 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 424911393 1250 424910143 424910209
    0xa0311360a140c0c4c1b02010c05120a0e1f0903080906040803011206110a030207031e050306040b01090302102c06070809040f05010308181206270706020d0e 69
    0x41401c2c038503441c17809032803c04800301138011380310300100c018035424502003210f41040d020f002c1d4180c002e915280ad24a071840701051020801d0f0b0142008808079911b04d0800440b00040061000d0301c1750006400c0b64002c82859080040c20820004600080c0c1e11004924840000610f06009a900000300360440c0e00b840150070a146000105480c501d490340440760390442981e0082c2614805540c0c0541d50703082c281009440f030900c0d00011011043c8050301c0141032544601501d802c030038121400b081b000e00c242c1c012904100541c002960100307481b4000c56525400294400311003030b2030070650b00c0c0a09019107081003030010850041d002042042141c00190701c22b00140041f8000610009005074a032850500700d44c2c01340c100f203907510030005640f808294444104c0c031080c40c003210402d8070b030066078515588501014003002c04284e05403940350340d600c84e07040358003209000c10000c0391211683d4080007503030303a1800281207020948030035060455091014800d01180b241041110b2031034000394032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 424912643 1250 424911393 424911493
    0x620030412031509050103110a0b0c0607210e010207030e0111060105010c03090b0307080108010b120a0803040609150b040c03060302060702010f0e0a0311360a140c0c 73
    0x3032400503e00001d01007030600d8984107560180d806030725800142051903003800481030742600120041c1c43c0500007a00c5c0c440340060401d90040305841e22192114002c0111a0502483c1150f0000d040c14410700190120055000e014803e000340ea4001110803c00011340310039850000204594010100600455004102c0000110710070314049400640e2000290380d0f507002510a1000204104010459503009002d0020130300c0040b0f0b1309004051313107246401e949100000004200120120018061254951200b000d9035001f10080b040c0b14103904001c0c1c000c00300310411910a44c80c0507017502c480d034402e1150006603a8003600c01c0307284c8400c507001541c0c030385170b8200d0300d00810690f4038040619494414032100150b200b16030060310400e802d0100001c08ca10070051b45c518111864040200011f4028250803a8240b40c05000c000c0d15600b155901030040191115034500c1248180800102d030b000052000c48040fa050314150301131050081149c0002001d01c0d0a0100b907a0f907800c00442c50070007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 424913893 1250 424912643 424912661
    0x50c070e072a1a07050406030f020408011e14041a040620040f08061b070303110417100c0806011209020307030605040c0602010207201c062003041203 66
    0x2460b00002c2200746164000580d00e4400da2104112011035030200a80403039000321124003192804100e00d00454014060f004500c520400c050311a80c8a19150105504680c06041310f000288200303072444403801c5502c0d01c14654291740900d40346903094118080180140500d62100f0b0990080c010402c414851034000b400c1178494644d2441c800080c1c1003078088010340d10708264661a00d031450840307102d044e0201540701c40101d0300b011040003940242c03040406102c515900d41c031610f070009d904080300100707584120301d111f50000150108000d040000100342e4000000207e0f1154144a03605d801a52002e4604a002c90724940100348650701550b0542c0c4086090080000d072090541c00103481d00c846a8425554245d5510600c008d1044441100b8040d00103070000307500d803201b6651540c0c0f010380c1004050700b0300414842080000c0d92480704501041e01c441041c40000131003424074a008000d541007420b881111620700800b5080100d088c0d0380b086030411031460b101140b4a034180c0140841307030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 424915143 1250 424913893 424913897
    0xb09010e0306092d0d0f050d05090c0a0b0a080a050a0e0a060504020a061d0d0c080124080a0209010e04050309150d05180d110c0a091506050c070e07 65
    0x24805240d6034408000c41841044840020600400328200003c0248500715000c1c00e4420311500d1054504000204c403043c1d20410b161501c82801e031480102c809008159140e40ca01e4184001c0c0b2174240c00024400300c00d890126407001c10715603900008480c61144900d8000800c4a44000603100749a80c2d00079030b071001c54608041030302980c16090a007450820314045440c83e91f0b450501096003407503050300c4040d20841c10f1032200d0f0010445901030f14643c0900c02c1d48502024502401080031a0300b40600400b022002401402806000010480d40c1402c044064000101c40025030080004134040310980280c40300c00c060342405041c0c400e4050042c016543c1d40b0081100032590707102c2c3d280f480310180c915032803651101385c0c480682099600182500d5034054958105007521400800c0c10f002c0c185150809101d1002d03500c5606003001c10020351313103a210803030440020707140244d5049214050048a011080c294440300246c859016000d29030036550300001051110704c041200705500540300d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 424916393 1250 424915143 424915157
    0x70f1d01020f07090501090506090705040e09010212011202040e1c14071a01180c080a090507030c0f03051203130201050703090e01030c21050d0f1704030206160203070209010b0901 79
    0xb410301d14584040c41d44080240c1d0380e200d00400602030b0905c80c40750044002c032108005400c251a005003140074034080c80700d84a802d0008552050800d60407920224612500f6541035030f0b68200b019280c15250400340c0c0141e080c155040d00751100803446400086690342c051422080c1d0700012200e26503000e4402061078020408100411000c82003110303a0003011502082d158100030f5030140c1014a2072030300d000304e401e000300600940d030054035040c5d02c6603c040000402503114101245801d00582c0040c24124a48101040038050901d941e0706031390191080301c14115007101010001e1100321400100c28030820081d1700150720810003805864081d1622604061302d070104448483c0b0280d004071083c0d9400c0350b003001041d007204a0500ca5401c20466031002c50119251161600341c040030031010045c002401144003405040c0a601d5028404010411440c003480c2c065910007096508a11100e100200309035603034800000c8518880c0d010b030400c1740c2070f40f03441c2030076070380f90400c1100a06200c21 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 424917643 1250 424916393 424916413
    0x3020d02030901021911120d021c05100e0405070512151603050a0b010e0f01030609091208060a120b0a02091e09061c08030603030f070c0608070f1d0102 67
    0x240c0055801008104001a690342c8003805001003000c22050744014080356002c6240401c0c0c0c081740911a820701d01c141d940d91a0285601a4000d12031420385031503a5101104100341591785511080c85000750740c140b81c0040351a440410710911084400030301541c400c40c8140180d06203010b003003180b0302d5203500700c0d0341c2c00d4106241e009050f40100c0786511400084000c16040540c940611900140190306c00c000801c2044002041c601382d45440c0fa0040401e140210402d074407990100c80289058401001052014900400c0208055144900055050000c00e500d490a4140c5604480f101c02111148100e41d03900c2464541d401000c0141565080c070820205840d8400702c9402820310b2a0003103081024001001200d40000c0c1010f40501401c009011040402590406a55070850040e90322a42e0f500002442d5101d41d21220241c1340000c0b690a040007481d51910f01555503540b61a0419514050200c50a081c1e020182c00060409901c0c4200480302c045c0c0c0300c82c42c403010b10541e0140b0f61 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 424918893 1250 424917643 424917667
    0xe0907050a181b0e0112110d0b150706020903010b040c02030d0c090b070506040611030606160c032f01021c0e030a060c1206090b060304031404090504060b12060907060e010302 77
    0x107200c4081c240801d00c505842c24585d070380100242100d000e40c1804001e110340c0d031081c411700350040032046174000c0c1c0e40e0424071499550398080441901d040800b140d40d661801c0ca4000040d4201488460180d0f0811440d00460b00c1c003030040d841c0c2c03401180c0c002c1d400c015034a00554003034400d000c80c840174040e0800000c50303404045402409010301a400a201c2420b162034600201c0d0114000460216014001d20030340c0e0313440c8030455009050020710401d01da0100e04010100c03481d15403004102080b2140080030244441ca1440c0c50080e2801d2211000301522005984400300724000e41001e103e45884191070318042e0a9542a42d00003600b03d403d20001513441e81e0881c0d42c0b240030440400c07600d2010028451141c0241d40180800310002e1040c090454049451070001400007411712a40107004071642d02070f80305070f0700244401c0308180301500700307410b000005149031724540f80a0301c2100581d15080d42c0000b00140640e5034040113050107444d001d811a2802c4841003103d04042e001c0000f180c4d408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 424920143 1250 424918893 424918931
    0x3030403080304140625021c020c1c031b081b03040819050d0e010c1505040c061d0405090a0503030406141609060c0c0512070e0907050a18 61
    0x5485049600e589083c24280010804031407200440140d0040c410000304640300c03600721002050700d0440410503050408107a00f0440e580183c0201c00100b4604140c0203603001490920786c01044d502254110307086450000e01000140020300407550640400b600941c10418140e03109002d81245410504c40d1800620707d61103100000400343d00114040c0b1500005204100180580015001c15410683d5840741c07242e800484020034402d0900c40c81d215640a8003022102d260302c110014900c4040e07801e00c00040c4010342d025074100820071400706109000303400c042c09041c0180e040d43d20b0056040e01300b03c05030100416403500b034040c00c4410300014808101a500561003500040307a1015400800e96190800804141228110307552a100c0f40d03821040aa0540740c0600e000300f02da20720f038180006507c0d17031540f015400040080090200e1800407465034145e4003054041825a142c841e110765441440c3d018031640400601f84c20042e918901c5101744100801590228881d15213071300041401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 424921393 1250 424920143 424920149
    0x3030504060f02120c0309070806090d0201060506040518070203160b040506070f05070303050c07210905040c051204060f020408030703082410031b0e0f1e0108040c05030304 76
    0x4651104144010030009000e040d8180000a40450503d0315001d08042c0d0010040c0010000d640300001084030709030306000303460280007031400300c80140c01c01e02080c2d642c62400c58240380042d46000000b00ba07500d003680c101c40031a1401003004628400c1d0010004042c0806890941584406c00803503140445079a0031000d01c42c01410511420702e081e00708103003001c3c002440c540400c04102601d0071040d800c001503440440d00340c40d00143c41d41c2c928890b8002d0b84501c18002c2c211030040e40c0c460203a04a2034070130380368541c0da03980c0e0409002da07504140415100c1c081144804140c0510070f1600c1e821141914507030207402401d0200c0e29900000203001207912540180c45560000031b404820316800c01da445400c0036551032028840440c0b2500a44106445081984541004504c070b01e190352180d04040d500755140d03008851040d059080c0030b0001d808500b1f1240c0100c0e4801c042c82c00c41d18008040f070505051422803040582d5032076004491220780204101c60400302020003007401c4d1001c00241000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 424922643 1250 424921393 424921397
    0x81501030f06080105181020071a2502070f1a070804080708150405060a05090a06060f1401080c0a050922090b0105060702130f060503120721020309100e04050403 71
    0x70141c6d00003c82d80c100f190782074546400c542000e001c088218030480003c2d01542118030900d0700c40817149800a0383c02c4004100d00d80c00321a440c24414100c810360414070418656020000d10700411010681c1ca8a02901c1046245000d001007000700d2041841c0034080d441c00600030340d1400c0d1060740e03218013036001a0007900441d0320522007440343d080200035401200090000071606850b03c0d0380c800d641d031500105080c6095440c0d00c04120f88160400c00395100030761010040c00b519450325614001e00c0c50a200704010b0041d0411000400c1d4018503100e40900c210094492600320b005005171590382c000c50741d454120800716081c40e03c1080a101000025402081c003044d13119607800c10061920068101e00e01c04c00d4100030141c01651504030307154a07510701607404102c540c0d603050b01c94010009507114503010302a0082c019040c04281d0020102248142d00b01c00131202074071b500c5103a1400f0300c595400580d00410814041d40342110000300241428078200c0d038585100b40120741a11011745040b40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 424923893 1250 424922643 424922671
    0x3030a05070207120f080723010c120908091c0c0602011e0b130b06091824150d020f040e090c030c0604050d0503070b010303021b01081501030f06080105 67
    0x74100303a05005181c02042c46a0321021039480c1902c40fa0b5049442c924028a2840001080c0f000c003c10b4210210390b440002c6100b19004604070310b07040c080c0c00c8038645080040e0042d030b00504c0d8940c0074810070461a4101e104641010f004000b402170000c520050307592428441e8824200242c11443d020019100c26070010411140c801ea0000301c1e60280501840c5a50400400394400e48940c4070088054220400c04503416404c000030640522440319070942100601c01982c10101e0000301d428066001c8507403070f00023007200c840f05c0f008541c404043c203648000340004c500400c42c070a5000d401040c3e070030400103140440d8505140c0d050ba10541c421143c0a101d2000c0224a90040c1b290050805058024280c0c54a9403400149280f0503030003500d120380900300c800014030000300140d83d045544044014200d503101d040c0a03541d02000400e48003020f4440301c072030750707194030403030016010344084c03003441109420200054000d044442c1c0d20800c00c994910001910032000d0050502409202c03079404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 424925143 1250 424923893 424923901
    0xb09310c32030705062703010f0e070906050a230607030e0102160e010902180913150e060106140c060118060602071406220914090a0f022103030a05 65
    0x840807818400703007103109400001080100d0749808048030000008135192110381c4100454440d440c8035541c08044d0036600c0c011003021011440ea002c50f6204203803608039014955540c1c80002070310090b000c1c141d00b011141300100303c000040f489003c09820503040502c079048511012425580105009800103402441c0348021940c051002c002240ca4003520007500b50300740310707000311740020600c00d4140250340000c5a5840c000a911030804668005003107001500305168442d1080d54610342c291081400207001008254252180f03408a01c074000c044c144681c60900b0940704c190070103e44070103004041108000002050041c40c2c041d10142c0d0480d600c0c01c1c2c068a4000c110380d000d40004055620240f824030811110300a07480785018200c806d180c1d90407600c44c0d4030302520a55410404034100c42100490700080a802005207206d11060781c004c0c40d42c80406480da42c0440d610060842c001c0c0d15410000340c1403401038189440001403902043c54514400e5500d19841150140c00c0c0c00e41c0d80e0244 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 424926393 1250 424925143 424925219
    0x170c1e041d1603020a0915020a02060c0c090903180f010306090504032a0f0f02150408010f2003071103090307060215090a03051215060408010b09310c 66
    0x1c2c40180025180440c02d00341c40e4803014080c0a00b500a1042c05c200403001d85805610800a65444980c0500029210b60149c964540c4c4c82c05d032208064400c00d0f00308001603140300d0020680e01060241c004440000c0700c86400d000e419a60801c90700d04058480d0001300d84644140240c0c2d0180e803182d0341d40c10001d406481c003441e5001030f0704550094014100811804901d83c01e0305000d00c5604900451901801c0c0c2c030000d10a51030030810030200d480040b90015015506500500f04660000707402d00545c40c0e22aa8040384200304407084c12449400e10101e080c00c0d10483c007401c12008035030104c0b480d1482420020b490842d0550140e00168400c21110080c5100c0d864503d8102c00400c0080204183e15600505540a04420388401c0f00320040050300c3c1c410b03c2e407880c04550001070140350b942e60720f851a1714081c1540f4408680299090400300b41e800d60b11302c10018142d114154289000d02031002818160b114403071046d1810b01010b0008aa80500ca02100e071085c080015901145030813030806c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 424927643 1250 424926393 424926421
    0x9070b07050c01020d05040f0303080a020c010507020a170307120b151611181803040905040807050615060313020a091d1b0105030402010509010c0b090607170c1e041d 73
    0x40c1781c1000f00c103200070400d00200c0d0f000581560742c9070820b4081580c40c0d40c6c02c54004d01a00080a20b04d608010900070402c2d00450f9030f20031035001d034900410080c1d24140e110039a00c41a9008000200e041d620791816405940c41703961a1600200350310014450303126206490380084003029030b184854000c032410808480900c03151890261742101007040030070446419920300a0590000440710211012402824401c40300a041810801c025508044c240f0014540040004503654803424001c1888103800721204811303000014a110700d5650740c1d20400800f502d108400700e03040b901c0c1e0743c4082440d80e0703a80191500b48100b61010710642c0540103a031840c01281d8a4000d041401201c0345030380c242d034413000300c990003034080c00c0065450014500480c0c60700841c1170060200305a00007402501100410258012140350f580c008039900f440b000d8000352001a01d030300445010800041d4094020b0903581c003038060140100791706060750342441c09a84041d0140c00d1414079070542c2000304202803a14 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 424928893 1250 424927643 424927663
    0x504081902160b1c020d05010311090609070e0409080c0102090a0b0414010c020f03060405010b010f11061602031207030603030912020f0f0609060d15061e0809070b07050c0102 77
    0x401400354100a0b0403000c1103000700d000700c41141c1000074000d00702600c55851103040d07041c0e0030411599501008101c0c2c000700000c0c08100c840040c0e01e014120203107005846203005080040400703007680c59400003901c849a001c0081a082354898140c00301250348207000c2d00414903860b0015a44010600400070595981e0b003084c0320300d803003e110034454220185034410300000b0070300f0b00c90448a81400061600140440a00d6061003034104101c20006c0641118103000020f8031035241c1e880340c0706800d44450005040e200d456034480400101c00c200e00868003021403a00780103980c90b00301e85000e042c0011030b04a60300801700b6120b160030410168407010303030401880e02c01951400500c482d0700045c03542c048001440e00c10005080320354859030718041160000e0200804455440b0388101d0548050701180d1803078503a00d03517a25800039503140212200307494044550031681c1c562860b000103540c11503001d021320516200742a004251028503400030030449008000620391099a030300020f2410b88900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 424930143 1250 424928893 424928897
    0x150415090e100618050c040905152b170d111c020a0903080705010b220b0607020904020d0c050a060909150303020c060c030d060b0406140903030306010e01021005040819 74
    0x10080003000c0c0030207902c00e1004018540422961034800c0c10f081c06e0b009075001a01054071b014148a01e4502910f440b0050345000d882107000e0300240220305441c642c2400d10485144045040074000440b42c840784240c55110300903003418121601584e60803103032500281d1414420008421200a0f080e811000444402031421b500e800985440101040c19600c0010005500419280d00f000b07020740140a0b01d00029040241c90070740a226040d441c030000d00100c010301d1a000d02407a031428608111007000342c02814694244c0ca40340c2c24092400c83e03840c0107035080e00601501103040d64504000c00006d021030b40d1110506d5042c00c2c52102204c160701103c0ca00b100084600f0400250046420003622104071500e0b6101c3c40e083c201e4078110f02c284244621f6051402c500840c202c20104003900550700035540354405d06258600301c003c540310380c0307401603455481030001410541c13003808202644c58ac10703c1909c1002803a0030704181583d10a60f01210707003590200e00407400c20804030548070311090358 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 424931393 1250 424930143 424930151
    0x3040b0a1407060905100c200f060f010914060d03080c0c0601080607030e0c0a0306020f0c010905010e0c010207061704020a0801090b090d0c0f080c0106030f0c05010206100b03150415090e10 83
    0x4001d01410803c2c140100d034001c43d031054410780c40c88009201d00c5c10302c09c20010aa9000d032a01e40c51b4030200403024010400d0903850032811401800d04d10001c5840f4801c041e014440c0e06246da1070036245040000e0681c0707840c070303010010341ca0319140074002c190090642c1d00050401d410416000b80a507054005549061b0b804251400d903e50b54200502003101e0300040b0041e550701000d2100c5205110340d4507030b60944c0d1308004803001000070541c81942091400d0060701d80743c0d1003080049071100000e100d494000f50030b40550090100019501e145c0151004207504100c540c0c503102a0b007900e45040c000c0c0c0320303003048c40100f000138a0b0134003410480c0d000c4e6180c0804008020760b50283da4104550b00500a0003000c200f2800e91701c000d6010310095504403001c050319a066151001d1340702c44600689005000c0e040114004401c6416200c050f541740046050841e0703145492075040c1c5003c110703515402620303034440c0c411200d1404400d80103084080d2000c6084440240d443d41350100c0003170b00408440c50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 424932643 1250 424931393 424931411
    0x19020307050d050a0f15030b010806010e160c0c0605070c050a1d090a02030a0b10050f0a060309030e0406080304030605090f03120903130906170f03040b0a140706090510 74
    0x4810111072008803080300000b05030b2904d5072000300404400c403420038200c0c0382031120000d0f1401d40d280401107a1150303d5150990b84c0ba400181e0f168402885410001c418203008241b1440d1000c4c1c84c42008582803400c40c02c2e43c4a00d4645d0030480041d41c0c8944082180010304d8018031511401e0740010702010340d002e04000f80782a0040c0c0c0000300c03e18807042e8840e400700100c1c11840b001e00002142d140c0040845100d00c0c1242801c131811a0207503481c407607080031400c000811382000ca55000081100500d143c048604e410000c3d805454043c1d000c6040140080c44401e040d40c481c03142d10060031782e02000795200c0b811454003504840c03001d4642c1069a016200188003268004200c5800a5501e80ca0301030540750f80b240345196008203000c400c03454900500210328002207500102c00c40d03522040c07070f9036800440d1007000e81303d900c0c5c0c9240b042560070400060126a4500004101049140c60b08e05a200301d00303421708001d40c2103140100d86458030781e00d801d000d0220401000c8003454002e0f00800c03c0e001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 424933893 1250 424932643 424932647
    0xc0822090b040623030312070e181003030f0e030105010611121303080f3013020d0318050a0e040309052e120c0f0915090504050a150b0319020307 64
    0x144d5011202120080425510241e1030610070f030346003002c8101140d0402c0c00c128602504441c103445c0d00358040c40b5139410b81e42010f01c4426009004406074a191110541075440c100c51416000c8454014000d04c040c022215403401d2080e14020040c0d544c82904c5043d03400e181c0c500304805c801c1d5040c1d40000a000b034044400c002c2d04640102e0b588a50026a244c030318501d07a0203a4025002000d01d01894040c400f50382c1400b0f01d60404e42c03141401c2c1010100e40e44d216000c610300c0320040019400c9a02c4c1c41c061000a409400000c008003010340c90207410540d1400002e820900d16005100d03104030312814482003640006009000e030108031250301a11041c2c054139002440d400c0d007004c0000e80032060307002085018100c0b06251900810303040c41080356084000d0004072900b03014800107105090000782c3c1c100718504980034500c282d41c1d00e00840c0d03d0881088041d00018140f02c807111b60f16000c81d1000c00542034503900410480d0189a01c07403510b0366125041000101080714201c1c010800c021180d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 424935143 1250 424933893 424933919
    0x50f0d021c020c0d0512030109090b1315050a1d031801021f0218090c030f2206091e03020f07090212010e040c18020903060a0209100c0822090b0406 65
    0x400903500d04c441c080840c10060b292040e1038101608901c0700200201d1030303404642100c4100b9009400000c03094603560b00381109e00c9604607000d031034403295282034000084503400c050341200c60200c0101da01c00300020720000042008181030559030002804050311441e10788c100318811330900140101110407075a0360520300c1c1c0480e100c01c1540d800221140c0c4665000070909100034058607103242031416015100c040d5100f5140f80e2010207800c0300148101c1c002c494290480008880c3c0401419150798031880946034030001191308240d640750740d40c0038007140c20b01004e115000c0d60050401e100d2030050b050074246103412070744895004010390a00340c540301500c541100c400c0b0944004a070303520b00302818a404290490b0103801403558101494000c542c0191031449811400d88225807a00c0044074120301c15002020f070840b6012036003500c424040d48242801030702400301d2131701d425039a00c104418812601140380f40e43c440d202092180708541c1c4148044c158044c3c80070000c00e810000401152 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 424936393 1250 424935143 424935163
    0xe0415030201081303030f05010b07060b0328110303030c0a0f05030c0403200a06080a0b010905031b060f07050106031217060907050f0301030c030b1b0f0f07050f0d021c02 75
    0x20103c1580e9413800c0500c41da000e0500302012400411032540c583c0f015041d194008503040e550241086204038070342c6400309040042080d01c110b0110b01360308021150107100f00b0510141c0740d02d800e41d0058240c64030184011031049a11a0b4040c1ea11030011402a0245c034000780f901e001c001050040028104001084805a07500b169800140b1117080b0703060201803400d1008079401040c8803d00046003034100402c50b0003442e16403002d101400e002030044034204203621a0a078994031084140b00035203203d014013500300c23030044e003400e25000300c0c002c02e41384039030200c101103c007603641307040810500100b22131000c000c000f10300e03281c1180600800d404513420406029140b140d800d04011600c207a002c2c80440d82c40c00d0300008510303241c0d81c2d00c1c101404403412521040e2070013001480000c8103131290005424100d0400036405040814210f04950140c00070b50207800a0103007003110001007841046140307215100000100030324401d00e00000d003041945555130188038030206c1030a00c1c0070307004505442d00d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 424937643 1250 424936393 424936411
    0xb040e0a030e0112270c12020612060d0c12030f080c120c09030709050a06050a1a07020a03020405010b0d150f140a0e0c03090f122d0301060e041503020108 68
    0x540c14030018500700824503600c240019000005501c0440310074050354802c42c50246c1c0e560465640e413640d52280301c03107a010009511440c10841d0b000300c010107241413500410094464900c2a095a89090307040c04140c010f07803405200c08050b0360400d40d102c200e01c2c1032001240341c0048070f414092507162003401007401140140da50100050b254045d5403003500c2403060000c003143c1c9400e81c2c601785030006020079206a08210b003071181c089040d050140180040781c03c680407081616040e06e04070f500c290010107040343d003c0c41c0716000002582d40c6000d558041e10301485055a070f1241c03a00c1200c1100c14441c0d02444d0813034000360422160b650320810350b0440b92182c498a1121070413800044485209030050700122005000340812040c08002030f51003200d645003103400e0044000b41c1d060f84e81c0300c3c0d2586070340c00c880c04100c2540c01c00d09060011030b2030b07401c0c0c0a41e005d0300009010404080c0d0400d070400700000d1500d0f50144010724190003041151813000014032081c80c11500001c010300002440200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 424938893 1250 424937643 424937657
    0xd020304060c1e1b05180601050f03070905102c03100b040e0706020c03150906131e03030f23010504051009060b0304230607030c090305100b040e0a030e01 68
    0x70140880b1120f142040e500800c42140f481207015039540c0e0101341c2c000c00f40100035810800015142c135519140c041c840584805003098a90660115154001400c0c00c04100c00070300002496251042d81942000131a211a02c48080752403070040d8060050510405540c000380c09144180c90105041002c485007150104000e800036002c90050052580484510f00c076800000554a60201c0d40200b020012015107400741e500080003070340b143c01079601e0b200b181c01030404607034000800035404410784d00c1060540500c00c1c0381c0d64020700c0d2070350328034060b00840c0e151b28a5030310707003502881003041795035110007a5001c10346107402c2c009a04505014090081e5622004601108004544100244a110310922034140c66042d4002160803c3d00d00305c550301c11684410301e004441c001403e070740e540c4c0d0034028001075035040360403005001d6000d4498280040e00d40c2c007002081c1d00340f040e0744007211b0160b004a03800074404184421900001c44404181e04003040e0b910000703a00c5080598030080910f0580c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 424940143 1250 424938893 424938923
    0x30507030510093201050103240909150212090d090311040504020f121c0906020a030f0324080705010e0d030e0418050a12081603200406020307050d020304060c 70
    0x2840b2030074080340105040d0031001003048804504c2c003031203060705c1081c1d900340724003008035900c5903a411030384c001c1c0101080c24020030f11000d5120740c0103409041c0154203201c203180348001c00300100e81c01001b01d1410810340070100800c49400300324024090410780b41030307814240785445501c1c4c02400410460311032a2100701280540d600c003100c0e6002000d0040445c0301500c21f00448a584802c4003003200c101c1c21201c112000501c4c0500000b600300c80791034020f00407951460364100d8400c043c100b14070043c141e03a000036440d05261407140b0080b15001800301d03d050350400c21903518144807170b44041d04018117000c0c000c000b42c80301c0326640a12585400c1c40280340c4040b000140140160101c82403030700f07504040f01814060005800c9150300d0041c3c0b600d081c80a0030f2001281c1690007120380e845000014200c989520344660f0041840010b0b01008100c3c00e86180509829648983d00c404010382c004289901400014010b5416440440c001903140c18a81240646030b00700c10000980034204103035140b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 424941393 1250 424940143 424940171
    0x703060b120d090303120b0616240618062411120a1815050c030c060103050c150301051c05011404060e010e0a1a0403020a080406030c03050703051009 66
    0x41c000c1e0480d05030a440e00d1082c60180184100c0e4180b00943c000b4203168804810f011481c861202281d5001c0c100a25012040c140007100b00d181c0c0d402129910140003100d4051240806201140700c20b00401048a80c03a00f900d9180300703003141140c400058500501000041d070124031054441c0c114030002c5112039040403050303c2901c0c0003e41d02e003080c05400c0403000d0100340f6170010100c08803551640095500d1031a4580f503001d115000310105c03681c0b0307400ca0580080c02880506208040a401c51740741c440b00180032410040b003030344203c6142d405080c01d40180c4c9451448030000009000748e840c215890180041c0103410300340c204400143c1104003000a02c40c3c00c0d00480c40368541001542c50701c0c2001e02c0c01b4002041c142d944102a94a0480c6500c03038500007048140d440360300142203440d481500c0010700410000074108074150f202c4d0b1403405000640c800041d000030900754400007a0504042d00c043c0c02e40700c0007800302040600e031904000380343c00c02c200c0e407405482400b080040d00500030a44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 424942643 1250 424941393 424941409
    0x209100305040302070801150501090b09010c0803220c2d0b070c150f12020406120f0612030302030603010b0f090a0c1116030203100902090c0f0d11120105030f0703060b 74
    0x10006d550070300c00c90303500d001d5110329450212003080c0d076125030450f81c0790300d6000e06019644003c3e001910350803401000c0b4920070040c42c0c0101203a141000550303d120800c00c40e8861791034080396170031300f031a1040220440154200c44208180300c000848240340142c01e0491041a00032100701910104e039420034018007070340d901c018140340420039a4a80010b58094040054a154800050502c40404103008a03500a0f00e04564039900c400d0a221700c808504805000d8010144c66400d80e0340b1400039541742c0c1110304038011802038800503560f040900c10300d401e44000001c6180140c0403002c0300c1c203050f1034101c00e443d400302c1255000078041042c1c2c0c504560012801e07000007914491480d0758801c00d03503d88090021070f4422400c96122800420000c800d8880511019510001150006506141580c0280b11004660706840c1c64051000e440c0f008840b004200c48100328408a1496118000c1d1080c1c940501801c90040001c44401d03821a81c0e0340805010003040d02d5106e100c66411503d031480 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 424943893 1250 424942643 424942649
    0x6090602030f090601270b0f060a0518090f070c0c09110d0e060105030a120c0c1206050912030c0a03060506030c0a08010f030309140d02090a02040602070801020910030504030207 78
    0x50565a0b8240101c07400420340c003d5a00c8079550040a00029884121115000b02c295200d400800c4d94808161034400901412030301e0364001c1030000a040c1340e540c0c9c1400500040c41c554444917104d41c80c0000114000c42110582405240e11406002c0c882558040580d4810101c0c0703803072805182c4a1a08503003226640d4007480507541011418006a05100090b04811403818010040510100e184680e9070101780300d0560550854500c85c0041403607901207010b084c1c41400d02c2a00c0750515681d02c102650680d128100581030742c00e00344108485c5002e2203420101ca003004103a2041c41d070389030362094840a030051000110005120003298000c0d003299004100050a203a101e14000c1c0c010160b503488484500002201a400031039200e02400091090f40c1e019a5440c050781d0610000001ca00c42c00d0100a0f031159019070301c4001652130b010b186100d102c1c40900541c8880c075180b000382c0360140c1a0807035040c50b40140500c444684508410607003491241c50041101d0325642000da0a10507150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 424945143 1250 424943893 424943903
    0x20409080d090606172103040206040807091b0c12080a0b090c0306010807110c040f020417160504060e161e02010b09060a0303020d031119090906090212130609 70
    0x11040400c1c0900c0da400041222a105410340c0b05c0550181010707107400f00c2c0d5141307540c10381001004e0310020f20b421000d0b41c0e12620141c4454079094a41c0c403101d203440712503448003a0490312500505100381d0414842c8959106038204105403102a50b100f15100c0940d0403818108900500000c00d0120130350441103904138050070024080c1448040440140c0c8100c40340d0340420000d074046161944a0700003d8110b11704080034249161842c01044054407040d100925000d0302407201141d441400b03071070b46c504505208004d003030717030403030107488810403541907101601c0b541c078095080000405106a20780d1004441c0c3d8004151143c0c03000560f084081001c400020f00d10071144942526015403000c12805000c8400e0000c66842000f00700301079189000013801608074241d9a502c01d8000d0b0440382203114854a0903003442508200640100d500401c00b4000913415002040f15920a00c20b14000e00110141035150055010400c640404040d06001c804c0344000d112500b445400d034402d4004c10303401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 424946393 1250 424945143 424945151
    0x403090b0703080a140f04080a031b0e090a0209030d180e0117011b050d05090f0d0306030c08030a0f11030d1b020633010e191809080304020409080d 65
    0x740c00c00415100089400c2c0380c0c81d80c540000b19000c0741034041510b101c0d40c00540741540d40e6590780d5420b54281c00541c43c9006040d00e13480281881c0740403000d50710881400b07680b10000c00740314404000f04000041e00d400e80580c810000d161403503c0114600180308070600701540580185441640070504980c41600510a5000003288045458019200300d1660400a1260460700014030010800f201c21080228400b0094002d01001c950012a40041c6038802d581c025040c41c1034150400d06144c00329400a0303030f160000c0c41009840404c8202405901c001182801d0003030501606004140c1d500c4070034064141c0100202660800484040c0021080d09100502003024034030440c030176500103040503000d090300045220b204004000c040c25601d6050714041c1c0030700c02c541e00e10045041c00c1d640c10032492400c0b15402d07403205607420400001d40007034a002c080c45c100c03180c500035603102c040928041c206034402c0c010604880541c1c0c0c0198048030005022082840c00c5040c80c4644403820a6450030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 424947643 1250 424946393 424946407
    0x602190c09020a08070212030c09090414060408030907060206011811160c180203060a0e07050702031212100b0315040603051b0a0603110d0207051203101d04050c090403090b 76
    0x4403141c814042c40283c6c00310b0b0480c0300d00884512007808101c42c5441203000c1400141c1071440e1840e4125042401429241c0603000d5415510341440d00c2141d0035900008000306000342041e0030810b80008241610280c0910350412a103005010144010a60295114907850f04400260b4044500e5060000703100c0380d80e021a032a001c03e60003610b21031802e40c030b41c40d01d40c240f10394055402100c0c49660010300540d01c0724106180c0003501480038240d001041810b002e0704005807410000040085e00c50000181c030f440d10405020010075005001100c6500c403807030304100d0079084405503a040a54420507081143c1ca844c0031038010700c003550004e440d900c121000405140402c00d000758051f8000d070740d04d003201510f030301050b8252681e0700002c51210340100320304400b102460b800b13441c03041d00c00c5058851095014000c07048a0b001960a1a18400035810401003400b13412070340608003c0448080000745001c6e22041d0b01c45a040c40e446002d8007a4000040800d0712501c4c10202070861681640d480c2e8403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 424948893 1250 424947643 424947647
    0x40519050a0201022109041e0204060e10020d05070f0f0c0303030c11011503020904061805070f08150106080720030a110111030712110301062105010602190c09020a 72
    0x10404000c2e400350280c1081000d003c1600c4400e514a811148143c41c41c001c1064140002040324442e00c0801124000565800101d80d00040c80280304a542c0c0304841c038480e42c1081010032221051500355888010565000e640060556a20540002c81c2042211080c100010803201429000b00108101000403040541590050700c801c1c10a990360310110410340c0c2c016080743e091030381a0344000c6c441e440800040c9490044980c0c490300c24000422408884092141982c24000048410390400c0e00e06001d00e99103a00321030020f01c9120018110454445081c024103034060003000101311401d80066011400780300031a0000c503014401c1e080c44608920820f440703401241c8110002582004070500500050003112044e0740074080840c9541c84aa0003a40d0411030300c8070a0700900d44035801c203187c101012014500a10507504c4045c40b808c400c4503210422000300d41c1504880340760500620500e43d00007011044a118241140e08000e20b034144649044007682c00030481c10f00004203000c800e6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 424950143 1250 424948893 424948903
    0xa05030d0212060d0506010504090c1e03020909070b190c0f050f12040503030307030209030f1c0905190303051803100b150309031c0609050a0605120313050904051905 73
    0x40501c450000716601e40400300103003a0b440c4c0b0301c00f0780658003070380041c001403400c0d070300103160b03030344281d45551580c0c2c3d072082d0240504260182e014910740c4074200400c2982400c5469681c000e0268020f00056410000218464010612800b0861219207044107410f8040c01e000f1a009800c40d1100f80111040d1505942e2003104206404560081da04204655605801507405854005000c0c40c10350352518400c400a400c0055102e500d0b10a00250211015081c041d50100c0000301c40c50010034420780030043d1140046a0050b03014000b81c01c0c0e100c030940c810305400c20036240e044c6400c0d980c51901c40401c0003110500b107900780e0306001e1003806044010081c2d102071401b14083d2003010300d0700044d50140781e10f07000840d8101d40307075003040248a0000030500c0801c404046404030000f1b15940318840c0b40100d503000c54060407800da686c1d105001502e800840d100580c0310840085141c204403004c0e03214801c40d50312916008500c2280402c04011050100c86840b440300400c0e02c60804d5641003140ea54 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 424951393 1250 424950143 424950157
    0x8280204111813020a1205062101050115050304031b0c0b0c010e0106060e0a030b06010912150f02040609050402070c03051203040303050c071106030901060f12230712050a05030d02 79
    0xa07541c00180540010f03072500995545040b143c885003000380c4a04c0001000c1d210040426030321548800341c402c06520711012400c11016200000941581404065003080c4094a10360003805014400c02002960140b01d004541c06400d800040411151034000b064146507000b5543e42c0d0404901c01100c3c1d201580100e4844c07000740c000b402260390710f40d020f42e05130480b1030407240c100004040600c04203072801a4250809810315103020450350340c0e610443d20103000602118000500015507034155100c0c00381c4400891040000c614151801e40e029044061a10900d0301554000c1812420b010412540e48001e64021080da09402081d81c00a421640200c404401107480c10001c102078030302d2402918025940300045885006e800b13800c20003a60401080c014141d900c0b0303030011034042d61900c110f60040010002a2a00102920b450394108142005110900700c003044001c419280001d6984226408460926507040d11420000d062a821000203000390bc0300160400c0242c030350b98018124 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 424952643 1250 424951393 424951399
    0x50106020a0b1f12081c0204051806061e0910020a0312051515070203072403020711040b03030f0319051302030606011b0618030207082802041118 64
    0x25942d141d060f218030400c00d200810018540402c2481360818502161a03641c2c00b0b900c0040c100482d44e8144940a8004401c8850454010400700402c0c21f0625100100041c0f80045000600c1c1040c0800d4282c040c030141022000c01e02c48409904601c00304c201c0343c42d40e0000d44549403102213604080c1d038079144880f0840024840000780714095890384101c500170448104898015040c402c01c000413000e145600d020a410200404001a54204503e000504a1070b001010300f4903100215080c0c002c0c4902d1440c1414010003032880040c021001e84070800000311000103603401e00030041f0745180a1003004000185001050218441e5011000c51048000e90b200740481e5680350681203a0103223200000350560b00200c040307800e41d0300034039031101c001600070101451000c03151100c0c025070300c0384410440715181020503c0c00b0b055040c00204007503c403200040c4051204040b00f445007007660150041c01410105442086590310342002e1214070180d0070781d0707803181201d018581c4184120007030544 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 424953893 1250 424952643 424952663
    0x8092b0c06020d02030403030c080f0316020c040c0503060d0507080604110f1c02040b0f030a0c05030105070e150304020a0e011401020106090e030f0f040f031a0109060b0f1309050106020a 82
    0xc00c07520002d140e2292590355400795090030f266a0381924a445220310403180f024003406130506280303103000078610407041d291015544c001c204901a05140c0303807841e890f0280381050160a001500801101d0300184141d0b407024100c44503003001c41c203010803a00982014020442808240440882407240c2900c04550240c00c1152880400004541925486009268840b038060151800d9409116540406040d00854400b40c01c00079040a0401c10200d0341c81003509000d1045080c02d118040d88000d003810302d04940085200010344c240185920010700e68000000a81107440350030f5140024200040d10110550b11141c04401e002c0360302681500542c0b80c140f000031a80702c00e0080031400c400f9100550300c1c5c40c1d1881c0780011264000c511500e1141020000064525408108500158020340c20580100d0074020b0b0148500b1041e48400400f500f045800d105a504035011144401c41c0c030f0403120790360500f84d41400380c0001268801c5000c18940400040c42e20303000716501c00351610031a0120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 424955143 1250 424953893 424953899
    0x7020615030625020703021003062c1605070b04140f060c0415032a080a050402130915090309170303011406071403071a0a0902030a08092b0c 62
    0x160754503011900340c5040740c2c101c0c2c0c84422001c0c500d009441002100e00c10385182a1b103d40210744038110381d802c1e040000b5503d00c01040084481614440560580c0d8417048800c01c2001c810703040d065014006d41602d400c088000c202030390089040311845035001340ca804080c902400d14031444044d00300030070180e00900c0b005107908480458110301c1264025141800d0904000f80f012100d80d050008406059955500748000d034540e070282e02210f8000068400ea101c0001c400500001c0b001d0981d0700c1c01c505080610006aa403482070013003410300010700240003071007428040703540680100b2004a5600d0503a403a41410390001c0d060003600ea4500c0d4101200041c1016140d4911003440342c10041280b0b509086664a40f0750b008002841c0030f0140205070040700b101c414150380c0421002c8907031404003c1c21820710908a42d8150b031000c04007030100b01d030007c0d94000c240c41d500c00003001065041c00180700e010650315200e001410001550505d00c003602c200301c41c4402104400c1d030645036490400000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 424956393 1250 424955143 424955149
    0xe100f0b0306030a0b09030c070905101706010e04031e20150c030a0e0d0309030f03050c0304110307090f0f0e0133090c021b031204171507020615 64
    0x1c0703000c0c800107801424510b00d2130701c9641043d17101428116803030208000c0741c40b15800070000030002e0700c2c1c124400195810102c0d180401c7c5186a400740d5a6904902c020101081d13000c6403c40c119684001003080700e40c4d0f28941141c690131244240313a609820800e01c0101d4691082000c0c004280c400c003008018501141d01540e249c500110300e903620b51500d000a4a8185513502960708413034911408141500001d401724144441540403c0c00260303940c0165083c103900016078554000e15040400090401c2c076160102c9210040002d415071800c19000e540b562010443c44004111000040100e1000203d802c409460420349900a1600b800e61215280c0d4061041d25080801a40103a010380000f50900708440c460703000b05040850031500010314001c0c54015207501c20880e901821081000c0c645940061605150081c080d81c0301300c0100038403114844c02c8071700b9101801d800390b94600480070b0303180c6401da074810200004032183c024000701540000705140a441c13035a0050707800040710801c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 424957643 1250 424956393 424956397
    0x5030309060f090a020111030904060806040317240d080c011515080103030f09030204090c03150b0907050f0c010903180602010b06030a020a03090c0e090c010221130e100f0b 76
    0x8884016002242d4040046d03010300355178401494408151790618540760002002c54406501c910040e13000700d0200010142d00010990810030540000320060a040482c40001e0040300c0c0c440040c1440680140c5e060368421a1030010f0b10b500c100d82558070b0350b600d001c3c94064891840003604083d604080031031840102942041d100c81a60b5440d806230703280d500e017200c1c003110000088050000742e241c003001603200c90240744031450140100c054101c6c42d40c60603803454001400140415803501c194002d0345c3d2b440c002c519400c82c0d0381c0e140c8561240c901031820b200c14450701b90000b80c150321b8800b0036020135400c85001500c09220350075104103190746480607420b9500b2034500e0355101c03208200050f48000168042c0042029a2800280da203070365a80712110242a504403044100e406000c00c000c1650410515001013000e01c080d02c40c26100c220ba034006203040e040b11820b14031004c944180280b10b030504020041c10751092600d49402c00c0200029801d41c1801040c10303030b4234900d5000c5016944032003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 424958893 1250 424957643 424957651
    0x82505030a0201030209180709051815010503100902033c040227040b06040f0e060105060309012903010506010504050f041509020a05030a0c0c0b3105030309060f 71
    0x1074403000340d240d0700440080d4000c0d22031580c000343c0e0200b00702e6190740908400d0700c04c0da40fa0711049000c40c00c0508108980303000c282a0700c00598880308102d0a8020303099108090307402030030310136141e8a5072040c071000364070a0781249040350b00c00300c01c0200b45c6c0c9210701c200003142804800c40b0001d455079560000c6003060040240510303084640070030018200244c40711400e017003000519840030441d07a000c00301000c00303650035111504403038244044c41c50280316541003a0008103080106c8841c0350145601ca14051103410312520000c00054500e0700c0c2908110484048803401e090b5031514415110104442d000103240030b036203010002016035000340101c9050b540300a01030740c0e40c2c440c02001c000c09408640b6150701c82c003541324800a4540701c0c90015086c418000c3e2101034580c42c010003601e04480c40c86800744100103d03c141c160204444c1c5e03034070b10341241c000c440d1001e210f09d940c5008400c0e0118610780c900908403548051042c0303e0040043c501800341801a2441621b5051410b016104143c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 424960143 1250 424958893 424958899
    0x703020105062806080c070c09051902250c0504180326060d15050720010c080c0d110d0f140108030f0a0c020d0c05030f0a0c0909020f0a082505 63
    0x1d1024080b060250507525444800c2c0400c541c1f41407055a11488400515030000c0e101d10f403540144028000c59911003030314070b131031203100314140700c00d410140018406000e030001521421038108410300c0074101026010b040c020344207005010032400030003040c84942d1000da00180304d841c0204a1f000c00f03151441d201c11000d01200c1aa501c5600400044032441941200c01c00404030344c420024110340a26441103c6035255003401004850003004a928850741c3c070b001c1039240c02d5040d44080d40000e8901d41011a17100d555403500f5101035040000d100d0180d10b440b002001051842140d0b405070820038081001160030b1040b444c5c440c20703403038860b94280100c0d201500300303010025001d103034400544540030107031400c00c58082e40d03a00441c0c88003460040998003d05441000d00503402c04002e2451424403000082c0499505521a885815003d01540044544801d0b0b0007003907646000007140d440d20020070881d1040da4070007a042d6960450b10104032406107001d1414001c0c010042c02d00c04890003d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 424961393 1250 424960143 424960219
    0x1208031b12010b1c0507050307120207050a0b090a14010515190b0a02070e01090903032412021302030a06030302060601020f0601290a0903030e3c06070302010506 71
    0x105003000803d801c22400740b85413401c40c20040d0007588080c040c02e40201d03840d46075940e0b82d040000e8024112019000140c860302d00401118000840029107502c07220b4100c00480141d4a40f00c10030380c01d05480950107080601b83d40007040c8410380640c0000d005080e0070b6803000380e000c100ad041c01144001c2c1c0107a00c0034a440103500700001c00c0050010401c02c1c4840c81940c0d610f6448201e00789210030700313810506099595000c0c44080503003510a0644003012541c2c00c03a80c006091042290100c041d0003002c65020901413080300710745a440602d0003081001c4002d40d200d02c2c0c060b0590300248610700c800d82c014881c4202081d8554004605e26002840c400041c0c041c41c1e00300402c1c21b030340310035500d01c0305d07060784000380700e081e00086400c0905070050240e52140041d618505008005500d81c2aa05104600e401e4014281c1004840c0014101840e008248442c5004204007203888a40d038141e41e400440001c4c001c002c040c0d0661009100d540b00b01c0349041518001c0400b10102080035400003500740071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 424962643 1250 424961393 424961399
    0xa0f241205040c05121515031f09060203010e060a0906120b060a0b0a020f0c040b0109060305060f2814030a0f111003020d0b030111090402090a1208031b1201 69
    0x201e82106502c2400b868515100c80c0d611004504090715200403194960424030385801c3d00d901551009401888030450b003003081e106e1000090f10388030340003400e20300c04020762480054504107800440306560441340442d143e46c2d581c0c1001031084401c0f00d40c00d10a203400030001c201ca049a209540503902d001080f02100c1c81b040d0340d000070564000d003660b0390290340482d00081541900c4010505c4042c070740e01418007101d100160902e03003101c0d04801881642800788c4100303d81d0340043c04500311042e034900403500b500c0d1000031030240203d02604540094102c00030400d8072030f400c400702050004511421360080d0781c1d01391591340e0f26100b0481c3d50381504020a65000300d04001c0001c40740034080ca00310a5180c0d01000010701c41d4001e2045200802c0c1c01042078100d8611501c03801c0e4a0b490705900034082d00454540415481c4950310071613200700d901182c5400740303032a0340e920708014000295801d0603a508600780818140c00c11540142400050030350041070741e882e07100361395020015040948903642 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 424963893 1250 424962643 424962677
    0x240606030c080f190209120a05060106110a060507121a01021612240203131205031b0c100207050f060c19080402010e180906090d1b050307020a0f24 65
    0x54056801c0c00d1007074003405121b1455407843c1e1010001c1030348030000e2500c0361051404a007002c9050744030b001400790400c0311101608001c0350103141682c0c801000509070350f50031001da620a40d407043d00e182c101d00d07001c14413a4074071189000d0070406000360211401e80c0c1d422600c24a191105000f82c4008007901039400000a54101c0c40c070354007001003210f041c030001031480001c089070011140d10400900c1c402c0d001d028010030248440c2880c1d010b02e40342e851450200d00440002912103c00c55610b580003d0280000601b48941c603c20b0401070000e554440042c1041e9603581076085c40c20403203000324000700c0d03411800c5804840c2c258680716000480c1102120043c1e41002c2d0080c016030601540e0010b0403001c0c0da8452013416204001503020140341401c2803440d16000009001702d4041d8000022a41025005a0bc0c00e1003071170650001c8008500303600d055402c0d40228800290010103c003404a5407144000031b21081d503169045540c04550a10783c85821142030a41c06c00110703000d0a03001d04002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 424965143 1250 424963893 424963921
    0x5040f0303200f0a0903021305010f0b07020303120a060f0e04060c03050103030f0516060212070e0319060b030a1b06020f01090209040303050703110a0f030b0a080d050304240606030c080f 82
    0x1c8401c1c108040301603600c0c0c000c20320007800100704a10b08d550b00c0c030044c40b000c45a003c4010140803002c8900e410444260302203a40c900c02c494405034611940c1d80001c0b40e2151580160002c1c0c01000d00605060f070b0348040024901006490445515007002c0e10035054500ca481484c0c100e07501a91084000c0102100c1922103078040140e04603400503290050000c60b0550001340714006520021001c10301c1c141c40007c06403c0031584041c469000541c014880d0345d80300301d0212074560411400202c032410440001e02d00802090b00502070b2040c0701c81481300004e4010610100c40407502034503c0c140241041c2c6080b0b030001070000754051705107008140460f01c66441958044102d05000503403403103040d0b040f0100c0e00a8000f20340000c207090798402025606000b0301c1c0c81c604056400806107802e103d46161540d86e20311040d4100032b004000202801991004440080240600480c200326506140701c0030704481d00a11011034103188111411521400c4194841d00c8910940740da25218a62a56190 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 424966393 1250 424965143 424965157
    0x903150c0915040e070c0203010c020c01140f09181f060f050a271401030b03070e061807230a210b1503061507050c09040303090605040f0303200f 64
    0x4503030b05000214074003201c0c0b00d20341e01a4032a80c44403488909284109401e440e0450b10400440d000b150400ca603998110340001e80895035084076617102c2c0003a54088200c0e002d10800f290340000c50456100301d40700da01c1c100d0380c041d8070700628200301d8503070702d2100c0d42c0904071910651f030001d0611588154518860800780c902c443e0701c0d1502c1001101680e010310b0703c91002407164070384001a550100f0851303001036150058010300307080c280801c000080002c1e03200d200340d120b412140b81e40d020000c0c0c03e544c4d1b40302103e2024100300c84110030b9810308071001000c16504020100301c04298032580d098861062090303421a2103250303505200d06041c40203400c00c40c0050500716407100d491300b140410941d110507900c4c0c100d03840040e0f126101d2501c442009102a80c0c0341c2c0d1240e9900040140c10302240e40817800c6040100b05940d00751340c580769850111300906500c40090300003417412041c8003c001c082c031207550f82d1300c0c0251b5051100c80040208244c4003510070500320190082002000c00307052901c00a40f80d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 424967643 1250 424966393 424966429
    0x8070c020607120207090e07030b0a090f0b100b1c11041203030509010b040603080f0a05120702010c0206161709100204060807180e060d0f05120903150c09 68
    0x401a4158040340494219010440c1c0c0184036800b42a45a03904000802c01040e0b803d20510648070b45400c1540c407070a041c04081c0000d180440040ca080e8001e401c41c80601c0c1d40000b089581000ad400d144112003010b9079445800111010002409468003007911f2104004006851100812810340c00041581402841146c0c00512000802c0c48240c02c808040301e000f030302c02041c00c5c640483c0d018211004184114070461406005101140030003080d51004409400b902d651404000d1080e29540036045801e9024504141001012039040d0850141c0708400c8d001c030381c015122043c8042c1c1050150000a00081d0000880303100e0700c5d007104000f42c0148000083c0e03144800a60602e0341030b64043e4000d50301141c050380502022540c4122050744020802606003002400c3c481c1c0e80380b948070040c1016201c0d01140b039480040c0100704120781e07900343d840b108450001c0608400c3d43c1854022503c0c2e227220303004880f01000e582030204201441403d0421500c3e150030075260070008150318010740e85074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 424968893 1250 424967643 424967657
    0x3060d020a05100f03060807031a070c0f060207112211070b04050c0a06030e060604111b0615040603051c231207050c0c040c020331080708030702010807 67
    0x100c030740720350f00b81150035145075071440d03550182001c010302038894aa010003c0c0d45e0160904001144605000c41e60400454000c0c42440c0c80b214070032034000041d0f150242080307088003c03085c100a120b5006260003071244110104144401080020400002c0040360300da990300584580b090010742e00100c4420400070301d45040140c19140e120070304004480499140d48001e02a95451500f6624130004281c18a41440026094100d25455110240c2150b002c0c3c0c1c0c0340c50100c48031069003410b0302c24180700c80032180d41560701c0100c80c9545e12000d40e007540d40040301003c11207203811b05000782d0096941040c01419038544218415014041c1c0600c2c0300100711001c400340049604201c1c0132091103450180e6540ca1381c4001b084119545030240140301444020814400e08038804101001d002104a030001400b403081d010590a600c18052a40200c0805200c80000030402d070298803085503460000c0c0c852551194603440e42c90040d4059280d051b882803104800544c403441ca034a07840310152a04103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 424970143 1250 424968893 424968899
    0xc0e1e04022202040902040e07020f1606030c0504030204090c090b0f150708090a0308030714070506040210120c050c0c1008191404141507090317090d140105010b070803060d020a 78
    0xc0d049803c15004012350320229014072070302c1c0d90704128070444040d090000d004e01a804089490b80c05d8490322a8000381034403108805c107420300401c00d1350003c0d90090000d00c40d059052500001e405040d0240d61101860f0601c41492030907c140040c1d03811101400038036200f00c0c2d00307520020035040103508540090341000000150349400708070400440c41032810a407241001d40025080c909400e400c5005e0301401d1040703c002c50360000c3c080e508140c054559403030fa0201840c04070b861a0b00c0018080c4080e0600d0000e001c21135004009000441c1c200040d2062010b2882c20000403903604408200050642c001103421718115000c11039850715644000a40580680001c6050980c1200e0649041082c4016222401410b010103030b66002c001c61242070340d1804100180c402c400c2c4d4040942800b81a03840c0c0221903843da01282c2803507030010201001900c0500e0324411104002488940c5542014000547d00c0c691800707803451030f81d00001c0c140c1996604010300140704102d01c0260390000b0502000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 424971393 1250 424970143 424970159
    0x10b030a0302060103060b09060a09050a090b090703030809030a0801060810030c030c142407020102251d090a060e15040804141f050304050a0c0e1e0402220204 70
    0x100c0c6268481c0c1c000c0d014940c50b60404a04486294003038034000d9201c00e01300045030b65904075060903030701203034000140d0f03071201c2004600406000d60018102d040340414041d03071090010f0148102d034403954030318003540d440d140b210391a4007881c0ac4110106021800520419008607111030744a0f00322080c21b01100d659450384114400c40354004d80e240c28800109220740e043c008605061800306643ca12894880100c070350112504058040b030f11041c0101e02e00c8216882070040c501803010540c904001c0100e0507980800b40324491160300c0c0003542e41040401c1048119107030901c40d0786684003912541007181c441c4405003114009000103401091f07a0340100154410340c032406240681d4640d901c50781070142509120b800958a184121182021030204800008204814048501d0641d48a445d42c2c82d080f803030f103c9800801000004034910204e20480c0c1251010703c80d2150f41582200c3c0350035200f50500d480e0060381d02030340100c001d401c01d107003541003594200000e0501e003000600d0142d9850b10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 424972643 1250 424971393 424971403
    0x14030a050f01060201090b040803060a08011a09061e0f0619020d090512101a03071503060501261803040f03120207270209040f05160f021b03010b03 65
    0x6145295498040c8520424002000c6014003a140000c1040c04c1941d12030528107040104020001600080041c0355a1101d4680340700808003080280121003420040013503900e0254100f500882648002501624290150402540703d540780b0094584d50380b001c0c4102d00d01c0b2140c880d0742040b000c02a03069081c01c01700c00e0032000b01740342d07010340a0003141140003000110160720051107502d184550905908011480543c5113910f81000649110030444801d554185240f50a40c103002e40300002942601481c040c01c1c0c0c4580d6a070f0701300308242e1510015580d40511500ca4050044150011042181e0301c0c020b20340c000030382100c001c810a81b444165481c59209400000c0c0303804512a041041000081e010b40c840d070794038000b4241032810110240d0b4046900140c0c0c1c2d07200c40c0c2e03003085040c2d500740680c11100380e584094070a2240c02100082c4801604040e2201e01000b13642510b1804a28420100075140052540c0900703683d03140c0241c1b08540c0b859000001d54155600c00e4000384039901000f07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 424973893 1250 424972643 424972651
    0x15090f0f0d03050904320903030c2a0307120e040c0903030c0302100c17091209130908070303050103120c03020c01050901020721050607090302030715050d091407051c0308071403 78
    0x1c642d4180d03c242c07158400c02400340030720703a0540c8144103110004ae0480c06079044004210084422130105844c40001d88000c0c40ae000b0090000084c0301e001e200f201c0404101c41c1086450b103800350205101400200c461040309107001036402c000500000e403144005c000c04030700a20458030240c500d180e03601e08680001c8145400305020100c1c0128220a2102c1e29034881a000080c09130700034012010702d45842840c5905106000704903e0481c070011350b1f801001d405400c21081c540790802d51a006d001000c0a002c00e55034001d41c4202d900400744a2140c03001440c3d490350260900070342d020b0041d95550441244a415800f0308100800d600650050540340703a00500301c1d00001e21040e041003420035101074110020405445018009a100082d20000300ea0f0307101c0c030901241c92003480403607150103449000310385d181c10200d0100912200038046a404082181a01d920b141d58200300800514a0007101d102a41c102280c000440e014142141d44204541030992001d242c01d204100198000c607 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 424975143 1250 424973893 424973951
    0x70201300f051801091109060a0b120106090e1006120e030d0902010315080613110d03020f070506120402040f0e030a0804030206010b0408150702010b15090f0f0d03050904 75
    0x4000c200f42600c024070103054403503051008001c490010f89030a507840541800c41ca003e00700540214000b03448a001030801003480070740e05500c43c80340710480001084c0c20310400000680350500071450080b2034550a000d0030b09880002c08031b51a1145c15124000d0308003941906513a0742d00481d25507582400140071030742a4820004a100440c40090111007140111024004104400740052040002c540390010314040e406007440d40d80b860125440c08102007a03235044280114100c0405400143c248500242074068078549901c50007406240d00070700d11065030b050f5a400100c3c0250500d40d11003034050501c50400b00b0005020314046113183e01002c079280000344010208814544d05001942c00740244012252070980f030702604075034a001e030614011a0040807000308640500035880f040740a140904014515500c08803005440e402c071450b400c0c010130940e10701300881c0c60410106007511030004c0900c000288503072000c8445800c4001901d811590300c06054200076100540e50900b08051 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 424976393 1250 424975143 424975151
    0x219080922060e070207090506031006180c0302030603030a120603050a0b09061e0c180307170c0a03050d0f0203070204020708030601110d05180102030f032505070201300f 75
    0x103191000403600564800c50f80c182c44401030040c04c66021514400700c0b442d040b0085010b4036282c0c00213042280c0565400c900a2805000040600300c030341e1643c21100c00d0540410804000c1501542680701c21039030b066050b0000c100c100c07441030007900803150b011608000058025140e986407407521b84040c0c2e003500c0503180b8000300403080808008a0750700400f60040c0a00080d01d44c0041140d204000c0c0004c010404003040c0b510641d4a40442d240301c50400070103c40c080c0340c2c0c03401e00519a455080c910a0070b4028a185003219081645c10001100d40c060b0041c00009a0280115250421100d1501c21030000300044c40260352940060440c503070191520b543d8908050001520210340758080c070900380c102c1c036484d4400740d40100613114000c0034039082c5034500c184040103c2c1180f0a0070303071019100c80e0200500840201154140c20000300f020505821384030151401e031001d00584000900042d542d0400c0450204007031007110300c4407a4220390038070a29008104c803060710341c1c40d046c90128640d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 424977643 1250 424976393 424976449
    0xa0908030c0a140313030609060b18150d0816080f070302011508011e111b100b030a15020d02041502010b01030c0c0b160c0803040302010e1c02190809 66
    0x1000701d203e620402010001c0d803a20003600c1500440054520000e0315441c0d843d041903040c001144c02c8521a540004c182c1100c402c039440c1000c05900b000d650402c200c0e00340c542204400d050881269080c1c541100156003000e9220400d4408422003800442d910001401003144036103d00000d007484a201c0d800100b0240140c0f00341c81c0340c60140f0740c800342481c3c0c10501d1040d85200e0383c80d1139144000e50050089114112010103111a00c109030440310110540c4c0c41c00040c107800419000b10507401d07000207100081c403d80c1055a540c07031642000d001200e0303082426040803101d600621070182c80340005410b1070755500c0b00d08601644911b050001d80d4456900c019a5a410301c110b6400c1c6855007000324110003c5d0710f910060b000010000a9944959030f01052154002c4150500320b03503201c00c9041d5240340c40d15000f400713404c07044040d1400780302d03681c4000b07403041318250462040320b03142e130040c03000141000180b2001b00316031005a5110004100741c410a44500c040030080c03c442c1020f400030009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 424978893 1250 424977643 424977653
    0xb040b07050f030402210d09091103061305091f05040507060306210203011808040807050402090603040b07092301121503020d03091d04020f12120a0908030c0a 70
    0x5001040c0000704041044081c0e103003401e010940307411940540b81030b22003c1e8014840810b003a255040d5210500c0303880029030349164420b2003402030341c0c0300001c24024501004044802800f0540340181d015140c1c10040106818690180d58440011411140501140d602c0311b00c1c032400c000c0c0d05114035502e0b581044140309d4200940030044c003451404105891410b0940312030300001400000c01100540c181d03e0955409400050503000e03807594800d0a41702d50720b8050495801031103528080d01511800050900d018400d960701000041c0c84189075607907603958141c003508010501c1c3c051000100003c80d500c4a0180c1c2aa51380e202280c044200c217001c0b01c0090701c1240c07202860031b8a0344c107142c0d0842c0c4c10b07900825030b207080b20307816100752101c104585020f0312101c2c0d0726013001c5110f1070036540d00320301d40011a80c80d0b0b000c0d60094501d094510017203400c2c040740351a2100030ba07078543c1c004108120181022002403054101500d480c201c00b07501c800d0306a003182d00c51024100030340d00202d45041409 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 424980143 1250 424978893 424978913
    0x61b0f0614090601050f010507060204181413080906070206120c04060912050a121e0305100e040b0f1b03091c05191202160c2309041217040b04 63
    0x12241c0004020f990b2420340083c81c00f03491301060703504003d4040b40810401441d901030b6000717003640c00a641c2015081c3c039072090080c08514403a90482c00905d0104016080600c00082e010b60424030035803808030301c08207012860303110b074000700d07003041d800c0101c00e400111160030b050081c103105201940d55403502ca401000d0a04135000081005114400d00c80002c80000784805101d0344540c160b109440695426102007610600e6804042070b044e0301c20102c285c0c19401144512011240301903a01c0d2145100d1301101380499004011104c00c902041648040d1601c1c0ca500c4440c0201b00401c109401c1042c8815810965060b0415480f904250301500c00d0381100c071030f410f20613142513814102402c19914014810405040521801c980990b0020580e90121940c0d1004241442e004140310302e4209110081485000d507940705884580c482201c03020001403202400030840003407521552182d6405445030112003040c801350194030a07203441840800d078451405515220040e1620741019400b00d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 424981393 1250 424980143 424980151
    0x50301020304110924090a0b061207022e09050c04020f04050909030a0f0f020705120f0c0a15030506130c0815040c09140a030c090603020f060403020a061b0f0614 71
    0x1840b5801d4003000c1580b402c001201c03050401c580c00f0702d054440c0380c004401001c54200c0242c10000014a0928190200c0c007070901401640c2d00715907212401881e000e00032200c44810810b0dd81000013000c030b020750f00360000340600380188146c07070707240803640001422030b40000b6928840c50004a410409450714030407083c3c0c4042e88801945c50504e40710390041094100a80120034000c03e51f00030004103100b000303010007402024108130401503100c000559103070a00089003542e407049808038a402e060003403002040f600780c2c08100000c81c046210039005410700404581d0008a00d25030b080d00c5042502078102da05503075032540c0102c0e00b00804c6807500307603428408142c083e5040c040321aa025074060210000c03181c1140c4403440081d0074100103000e140840d4405001100c40d42808100b0025560042c0122071082342c0400104035034900380300240c003c3c2d203c00381d03026213034070810001c02c0d0050420280b0000b02e04003450554801350b940070000d948450701500d40595a64401c04891001e070076181e04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 424982643 1250 424981393 424981411
    0x1410030501270206070c03023a03080a020f0d14090d031401031101030209030d030c020f010912050f12071706060c0d0e01020c180912130506130503010203041109 71
    0x100300c00b140722102c030642c094400a001d03240000307002c1c0500070140c1001c0d000e0340d8000c00b889000c1d010341d803a201e6004118036051261583c544c2c0300c103454114011047ca01e8645c50780f1150307030941c0c2c2c030600a0000c3d041003880ca1582e1208001c146074803141441a40d2901034280040040b500740704035210318000b041d481c45400c0c145092502d120031483c6600c000d04681c2e12107010500c04080c040101c02034000c80300d100744c1511440c00260f40064168000c42c0360320003240d00322402c1d0140e5070030441c26204004000b40201d204920810001c521540c024050f80c084e1517543c6182481c9100e0300c0d2841941240e2a80008190305410080041c585151301c2d0814800c40300a42401c2c000e4002546440340c003c02107003808082d0460702201e900030310100c003c4d408028400400350824160784010f000c001c56083c0e5060155030b42203a04d0036412000d560f5041140d1076a113540608140510825600001c5080d41c100d00c0c0d2a000102c0e69400d00056202c0c80c42091200f81201041050014a48001d041c07122 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 424983893 1250 424982643 424982681
    0x20706110c0a0204200c011a0301090f0b1e0901150512060f1008030d0203191506110a0c06120b0a050f04090606030501050106020604050d0c020105030106030e011410030501 76
    0x70000c0006400c80015011940003071200f2904003070000620a42404140000010401140680041d4403200c00482400501400321980304100760880302d802000500a110054502c000305082d0208164407201c2030b03c54801c5e0f074011802d6203900324002c40307003c0340a03074540c0885040303001d800150f0340080109aa0b20942040065405501c4070380c010004114109504006641072649a05010041c0380b0311068942d2040c840460101a5004031a2550442d4003403509203001d00031441510300000349843e21100541c180700c0115804030111144410f1440b544000c0320200705d018841c00000d00103926400301001666400754162114100c030540320300420001007020340c40d5860400300320b8004590019080b207203854440000d00035500050400d41c600000070420039000103919000ea8055012514014007035a801c4a0301c040042c4000c1c0011303010b00040103014001c1e00540751240c410000400c081d5650309c50a2600780701218012404124842d0810600c00c1c00c0c41509440700f01041442 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 424985143 1250 424983893 424983907
    0x2a0e010c08070c03020640140a0504020d060503010501140f0d03170a0b12070311040c020102070c0305031c1116050309030a2306160e1c06050402040e060f06060c1e0102070611 77
    0xc0c1f80c00514030540300c0300c401c042081d20b1103076518501c0c0d81c0601030003041103445400c4940390348002c01c400c0c0034803406036103424000f20b940c042c0140160300ea032200401c0d96040c05041c400f441103201100e40c0403404d000600501940302c841e03076445541b0412003180001892200d200401180c0c003d030382041151600020300600c00300340c1110a0340100b40301510701143ea400402000c90080c801d0100240c41c8440048002c0100000032008001c80190550210400c1044e5131142d0100c4500c00c01c02181400c0411880000c80549088204002d020781c040c0c81c107042844020038180b00c0d94020403610f4501b03560048a80042c01c80c0f8440c040d10114009181500d0000c21900100c0680300f80501408500382c0b00c5602595503442044c8038000d0080030108003c22450404042c120554049100f203040803c01c0c0700c8007100080c803901c901d040540002698a481c41400b82e40e034040b03502041980207000006407031080038000e03408030420180c00180d0b6220309040801c1110348207613149a040c5802c1102c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 424986393 1250 424985143 424985257
    0x17010f0b040c0e281409060114090d0c0915060f020102271207060903050106120b04060e0708030a021005060a050303040611102a0e010c08070c030206 66
    0xd40303007810042c0c424102c3c2d00d6806043d00c00705240c6200f13200f1009028040070500c0c03000d20b02c6035600c0420aa5210a098407044010b446071403020340c40b6203111809000a0b1040e1030001f60104200340150080041c03280c44d030422805550241d20480c2c040294540200705843c0d00400995000c039052008505100b401d50100c81115110b0941c0981e022501e81c01c01156540c08076800d45803986803045801596807020003421400c02403100b0754280d440c10b00e00082459841440700790113070f40a09925069521640d800004015104050010b4400d80700041000300c410001808150720340c1c0c0082c10b010070340b002244240c03a0010a03403401405a100c0401c2aa200042690281c52613410014000c1131807103c1145014108000a0034103420a21b002000c46004240b4068198640c07054140c078800c1000b0035075000010602c2140060602d1035494045010356010b4410244224181079004e50750b90000350381034001815680d549a560b4103146516071201000c800103004d0354400300003013881d00d1a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 424987643 1250 424986393 424986407
    0x5160806060f0c01020f0705070e1e0609090f0f0a140703030207051c020d0c150e010509010e0111010903051312030806010e0102010b10121113030609030917010f0b040c 74
    0x351026800100f000050070030b080d016920402100c40f503031a11180790341482c40c0d881c4860700c500404403036000041110b881007400d8210120064441c2110365448000900100c444005c2c41c0001c01c0c059505116040d4005224074030b50380e00c001b0010305800321181080b040350b01b00d464000c02e55511022301000002e8000c6101411120126280d46080002c0244c03010703015000540290310207d414102010040c04900400645881003030381c02c0d1000074a542030350640c40c4458204c0c0030960a102d4204550302c1205950a007090601d0100981044202d1090940b0702e01c850072800300b00f020440d038809080700d89000e80109444c0090480c0800c150310301800881e0b000d86001d0401911085050f0f0b664000d400c0005030307a2001d0301941080d01040300041c00c40188031030302c44007076040001112840302008141c800800c0e80e00304034491146913560701c100030320411404401b80110b003540058045107000011000450020001c5140e03961318409004403140181c88074031841c81c200302021800d5000907 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 424988893 1250 424987643 424987657
    0x9060501030b013e0a03080708130f0219030b13030e01180603050402121906060807081c18030303141003031e050f0d0608010b0a08060a051f06030516080606 69
    0x55404d90700c000d102d500b8801c1100c02c490b07150390710441220303030100341e03201d407074640700d40c500c1c1c0e0300e196964a400c03000800100304c07850003403d982298111100540351039200f047d04032941441120320b4039504d549003084044221252845042d420099005140d0403007840d001c0c924003460f03ca0f2244240340d2041c07003801c420380948003c241c0c0d500c2c0000c0031904e0b02402101d01c240140d0448000b4250f032003680a0705016440f007192150f05166001410f8140001d004065412030000383c80307025000f1040e80c80c91b0301c0c008000410000741c10a181101800c10230300d18051800ba030750100d034820b41680e981070030190141c88041011211203042000c29030148410114000c40014840c400c001c800c01101c03140250b9195130b403c544000303600414040c496128004480c0b40300000c0c403030340c3c860710100a4800354511681c1041d400002c0050310401480e4000740e0300041d4a0618003104252104100c50566a5000300c80030a81e200c00b808140c00041071100c944080601c0d051015241a1020900b82c0c000d04c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 424990143 1250 424988893 424988957
    0x13050702100213090207060227010207060804050a120507030314011a0c0c03061905060a080307020d050114190e06070f03180204020705010203040c09090b0f090f0709060501030b01 79
    0x4920100940c16050303898004091513482591100900d003072400017584035080c0c8684240310222a00c0801c0e615030510714042105170060000c5038940301084c1ca140f13900810844540c0102981c450001c4c413400d2003085680e41d40d540700340e2a03901624003d01218181c403000700790032070700d9001040701680340d0398500c440d50f17481030b1407507280c090a00d496860001014080d60341402010100400301c4591034410540510303146091026440350028018502d141d401410340d00e420030480c8070003500f0031281140903644a04000640e01c400204c41e11030b15001540d0f640c880b9155a02c0c10030070450140a5420b132280500090030305410500b00203010500c42c02208010b0584030f003698541082d2104000303030781a070054419035031010149405c6000358011542107440c00503080002c40c10080350b11070003440340e80c000440091510b0b9408000c40c0c01400a200321302500c580f4001c01090701040c4840380c0105030413080030034001e050078000341c180c80185c40320b24100540f07034484500c080031105400324082c03605 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 424991393 1250 424990143 424990147
    0x3020d05031302010e03030c070905150d05030f0306060f030112200901030215040b040801021216050d150305030a18060f170a06031b150314040308061903030806130507021002 77
    0x80b9080d07000b02024064613000c0e055002899501640049220b0f433400c1d0850761188190008110203882d4406024110f60300c24000d11864948080086422010081c0901d05010a040000b00c03194401d801c81d0300c02c40c02e22002c075000c0011000301c118600d820ba84030801091f07036040102e0000d4105102c06031281c1900b000c490002d401c6103040364047c000311b0441c1030baa56251300d034060103540500c261801d2081c5490024441096223000103680b07001c165203952030541c43c600500003a04064229a215000041000000641c00c00060006580300d89801c0e0642503580e1801581c82280c0d0f00031802c0c000c2c500290450194000d880e0709034600c12604e5842a0740710b041c01c05004240b503400007084018615108103840d000e00d041e45086a01a001b14400d010342003400710705468000e90b9000c2c48402102c0230030300180c0a41c1c0710641c00031001d0060410350038185400c400010840d441a07000c00d41e4102800000c1c01c000c050041c00200d920814003003070411002c020764500c0300d1700404c010b4642c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 424992643 1250 424991393 424991417
    0x7020f01090911040e0115050301090e010b0901090920060d0518060c03240a03030c061118030f0a050601150e0a1d0a06030206181c050a03020d0503130201 68
    0x203503480e070001c0c00c8014010041801148002c1045074058010820b584440c04000038040c14140c0f181c41038002d80c0d40e01c041c2164a4140103201903c3d401e90300302819501e40701c807542c2039140c00c09610f0003800100401b00d511019030801804070b407000ea56101d0318040b0300d08000103941b1090102c03100305240d041c2c000355681e108055078041c2901001c1d609020300410f01030100340414603001d1406220032082503a070300180708134180c440317241c504407854001180c0441000402d0082c240700d105c0500440c0b021580c40ca281c4d00400c00b40d484103403008860b104004213002c5d01d0800300b00c960b00b08050705000740055003080d101e0300d9503050b05118080045a401b07060030400c6104200c00d00760110050030f102e001d19115651654040079214094128a8210002038154000c9000e141c040780e4000d8280351401108440c84410b0030740c42c0003e950481ca18029043c0411200d095404140b8020000b5049032405454020b0400c0c00280488040027418418400401003510004400590908040304070b1302e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 424993893 1250 424992643 424992647
    0xc011101060803030c030f090d121a0909030a020f060105090a0903110d09030210020607080403050d090512030105010f091a0702180a090b070c05072619111507020f01 73
    0xc155000660320f40008000d10401c001540c01030b41c001d20300c181c0390143c40d564100c80740340c3c4c13070b0750842200e00080d01000301920302d400154002d401c080c101c0d142c0c0c00300b00c41c540004034100e03050550303003c5081c0d40002840c0200725810b001c2c5050620034035016103415454a800542c04403070140107582d0095460700712100300b501031981055040365010a0781e1100500f554003814103015844141c0c05000840780340c0c00700c140302140303141c404c0f8000d031550034250f00c8a49007112503801c5081c84503411903403220f80101203101080307a8104114800742142d035941c101130005140d00740340000030f0b00b130240030a4140002e9030b9055011050134802500b5949a5034680009410b41a0322220a001c6404440a1280300100f6401c8074505a00480c00c800782074803001c0085802039490840582544c00c580f0007030141e8038089444400306000302c845003c511000e54000c5081a111200410055412100c10801c02101c0900d00c090503500301d4120041c058981000b035414456080d000b845000b00c0c2c800c80d9003a0f8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 424995143 1250 424993893 424993901
    0x405010e100509100804020f04270c17010501090c050c0a0807111203090109140a030b09121b060601030b010801030201051b0610051806011b0303020c0d0504090f0506030c011101 78
    0x3e800500043c1085079031301010780214800c1e14103900901038441ca070b15507411f1500420000d00a017031541c040c2500500c80203401d0540641d412203001388010400035490404030440c0140000c054000034482d40f424021004644001d00d007042441400d01800e00744100111300500e0990b04607030f00640e600c00c0f600c0c018031081801d144099010712002d520f1085000000040c0480c0002030b21f809102c0c0b80c40311602c050038403d81040d0b07903226403201c50500000b048218100c5d000304d400011100f0380c02c0b406000c04c1c100d82002c40030745202c4075000e2807c460110704100c01d54004070b003820304100c60452580020500e060500000e03061000c00500d0504c102e449803e00c80e4901041c0054403054105444600c502134a14800c1c14400c124001400128080300c1009a00404050b180c5c51110021040070f04051000603400364185a4284101c903c121030520400223000759036139400d41d803503052440031011510200c100c28400c520708401c004090b10700140d50403c92009007000f18040e8218000c1c24054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 424996393 1250 424995143 424995157
    0xa05090c040e04030f08150901170a060e03130f050a090c0203090307030c051e0a0e06030f10090c0e090c33030a050f130f0204090f03020c12030405010e1005 69
    0xb40200010801411361010030300409040503540c9000c6516500200f40100c502c80c2082030780000a0070040107454411080d4980d4840c0000a581c4009125120501101c860492883e5550400a00c0f07040f14455031035a0342c094000c50303d0001d0700c0d909107000f0405040d56800f44105941d0755002a91040b4020001d0b2881020002c0071560004c0e180d103480149003580b80719290007407001200a65104000994034445c0c02c0b4040e2920140c00d01c2d05001d502d860364003903c041c0e0140641030404081d4881070205e040004084ca0f0007043c43c14040c608032a4601c0c3d1075200d4a122440b150900410a1001c00c15014051007280c14408083d03580b003d62481c00403042c0d5100f6901d640c0c0003009500c900350301c0a07510030795025408002e11756821030080300c844412603851102000b42d0f050400007468040c0210242d50025100180080322555001569030107000c00380e025a01c50b05000c1051b203051030402d441100004007443c100380c030302000a00364440800846210b440101e01480c807092003a4152008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 424997643 1250 424996393 424996409
    0x160507031808250b07020102121e0c06040209010905040209060f0a1707050a0902040305100504030c0804030b0406050a0204260a052b0504030804170109020a170c090103020a05090c04 80
    0x1d10840c3c100420286000040d400b080c3c12408002282c451481c10b8848564060f0003506a80800c1411404150b0203002e240d0000c101982050180c40205809480711480b00f80003010715040c50b00410004910580c4402d500e40d0601042000503240c541540790000030030340d4440100d18114000860b26116074000120750420241480011440043c09008444041e50031001d440d8840301000c00340c0c442e40c007001e08190700c52140049170701403a0340540d0780702c0e00905c2c2c11242a45244d89001c60360b132003507005803500e50160060100f48019445155040988500d0440c501450200003050321440d03c45505c0070044610100c1e6401e10092280c5c0c1501c940c040c0580f45485801055551181000e1081300d10744841107003a070044900a004503420f4030781104100e400c0a24210101008a8600d144802035548a00b01e1400584984052001504240c0c140707900040030002c0f4249840c203903021052042c54900e00410140c2c6400e5421001c1e100c007514800c081d90748158030300324640319960040f04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 424998893 1250 424997643 424997653
    0x31801050a02130b07080301150504150504090f0515010c0f0f050a0b0a06030c0b07021807050d11070b0402092518410405010e0906160507031808 64
    0x425001580c0285100c40c00035000741901c80d102c4c0c0002c1d80b14002c00000500300181000140203840c4074810300d001900640c40d04a01c0c19441d4605011010341441600000c200c0100c0e0070711004034240590780c00407001040070020340c580300d000b016844040062690500c02c0310f084040620010800d00c1c548240c001050085001c2140340c07850fa1910188170549501c3c04100114151050340c4c0a0142100e03004114015441d003030405074205a4490f00d0126802090038581101d407111040001c0c0c031814480c2c942c1c50700c6007290150201912460280813561000810882c0300041c58008015041134040c0d404520070341d100d405c99101c0700d2100c101c000c4009450b0104070111540202800c18420324002c46d01140303540e5441001003420a800460f55906c82014804a0907802110700d0400d03a29000034244000c0283c00803c0c200c603400e800400c4503401c0c000c00c0040e8100104000ca0b000703070f00d0141009c4042d1a000c4010018000d0f540c00504028a1a90b8229010710580c0c4d1100039000c0707003041e10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 425000000 1107 424998893 424998901
    0xe0f091920030a03020d0906020a080d0b04060b0d0f3c110c07080d0512010b07020a0306020a0309060b0405070905061e04181104140603180105 63
    0x1c80c5040d220545a003150b80e810030a119010703000c5c0c0c020303000d00c080ba517200800101c0c03180c100700c09550061b0b0703200c00015914421200440040000040c0030745d40540000c0240181e6805100d5040020500ca0307120000d40d4451507884000d107004101d400d504002c130000411110090950310900200300403184040280050920090008009141582c0c160740d5107030b580240158140d954071813141801074860800c030310114080f25040c010304002c0992014841c2240501071441d000101003441000c54031440068406140d1141055480b25652a0002c0050100c41c0c0e041e95824180760410200b400d2511030780d401002c80d82d40d000c001c1c0c0c0c24142400841c3c1d020004440d03941d206061400701101442014001600c22500c03130800170100009030030152103240400108c192810042040f100c503e03906c1c1a092900d0a403162526a6106410302000355107481d990195542058100 = true := by decide +kernel

theorem cover : BRFrame.Cov 424820143 425000000 := by
  have h0 := BRFrame.cov_init 424820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 424820143 ≤ n) (h2 : n < 425000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
