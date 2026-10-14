-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2246
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:07:22.359855+00:00
-- url     : https://prove2.me/submissions/e4612ded-b365-476e-b1ca-0555d761ca86

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 403776978 ≤ n < 403956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 403778228 1250 403776978 403776991
    0x210051f1a0d060f140a0806070e010516030e09060a0e01120503070221070e0108031c0209040f02090a090c1d040b13090b01050f0a09090f020d0b0709060c0206030a05 73
    0x104042c03640700c0590712070310300141081c2c110034402138103050f003104400c000340b40e216114a0003010305100220002c907403290004180d041c00300b2642d04080050324180552001400491480602002410380042d0141000388044602580982e12581084450324180c014405001c49000041c0038022281c8030809109000300304903810801143e0000d03030108506980c0c992000c51a0440e4500d103241009154080c00b1000910780c095814402c015940740582550500400c1e0091409180004030303904940140e070024200340030070810024040040e51080c001d0300c0c014030302c65500103102c070031500c149848a03c0301e980e10101c810f01c600c84415400e440c0908950312658034010840c5a80e80d02d010103644104c236180c042410052803c1c084c880800503030140d0b00a10315241000e0080e0340350307055030041d50310103080003c81d1306141c10844203224a00400940008008031400b06121311004001c1c4214842c2c0e640c0110280c83e2041110141e13038a000c000d40055007403020800b880c84540110f0390245 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 403779478 1250 403778228 403778279
    0x10f1b081803040f0e072303060a0f09020a0905030c0a0501051803010c0e0906010903230c0901090e0733030e010903090602012f160507060210051f 65
    0x30380d80300750642d4059400b6510448020710200320120001d00010340c0300019040621140240c00c600c03001c4c6141d01003895120b00400130000d6490368891030341030f0152002d01c40c080481511400c41c40c000394028004040883d000d124001100d02d07000038200760683c005000c840d42c80380b038800155501c2c1c100341c507150007a214040700b40d82c058409210310b80400e9290b0b03448440110700c8800344044024050141c40c100104150203101046042c414002010448161407541c414156400c0e420710701d442d07030060f5018580200000742d10310b02d9040303007201030385400c140c80380559949000c90b92000003114148400f00120241180c035015001d8213844280c0c1400c0114000c00c003112041e0851b004810210041003031540306115041e424441c68544500911b002c1c03070052080040000420000c0340e000c56045400607a40b45058101d80314403406590000c102c4040b0f544610000e0b4580d20148028400340380740a0000b40c1c1c0350440c0706222981803241104200a50501c5208031007501218109a82103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 403780728 1250 403779478 403779511
    0x9100b0105071202030d0e0313060f030608060c030906010b04060f12090f06050a0e01020c0604060218090702060403020d0c0807030e060f18040b03011b0c030c080705030a02010f1b08 80
    0x9440303120403c0c40e500e1990b0182d5a00c0e402c0b1803245003114001040c1e52031551052044120100c00a800704041e2910340c109070010140c003039412005004942c100701424090782c030601c016942c805000d9402228218107a804980c0c0301c0b0741c181140d00980c840c0200050143c17100380701d51401801d5000e610014154049440e030040c1d141c095040c120341c8011500130350341d00304104010300c551007264500c2e240c900003946803401440082d41e88010181c0301a008c40d074001041000e0455166904d40d6804c0f0103000c0c60703110311f00f4080c041c0d10b8030000c603010740c0540100d8038042502c9210f0016180c01c01da01420060816100703840031940000903a02854201c0000c02a1080050407480903144490f200020f4040383c942500a11090b5131242007a20b0280e0b0500c0c210030921b810170307005090014018904200710021780d04044030390005a9002800b032190018600301444030110082c0004102070b0003c0c8452040004124115681c00044c0ca0f9000503000c100d089180c403510805810424052000609 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 403781978 1250 403780728 403780733
    0xa0212131a0705070204110405010504030213151203020d0311040b1e030a0e1c09030213020702040c1d010807050a1202070c1d011202030604080a0c051c020f010509100b010507 77
    0x2021015a82140070443c003207800b0086203020701070900e48224217200c0e03508003440c000c0041c00074042c5000092185140c40c002c540030f100d880e4071074002c00c000400b10504a6031341c1e0344c0190064180f01c1d0141c005003d81880c180e44c041c0a40144c500c028070f4090a1884c20b882c004103103045411414006411051080388507541d407481c400514010f164049002400b0b0084104131490b0588112807004840c0d4888911072900341c0003003240302201d0b016181440b0380d02000d080c40c0024400c04500a40c40f501d00400700300f40ca50b00c07011181c201301c42a800002c0d06400d0324010354880c03104980300000034a003003283d461418800c01411542c00c0f50f441015003080380701c0d07413085c650140540265100b001d8100b01c02c0c880d41d0406106500502c000341c0d4422002806802003603c03040c000f0b102806403c000610b00e01d09922525030844155080b400ba0789603414201209071004440e080301500522800600c18900c4a061181c513000d80c807003d005010400380127020b1409820325602c02c0b03040c807800f031000602 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 403783228 1250 403781978 403782023
    0x20402090a031506090e1b01050c06100906090902130e163305090d1104050a060e06030d08150d080a05041a040501050307030b15040810050a021213 65
    0x20b18840c0c25022108207600001604885065210304003660038003054041d0703030381e01040c4920701c6024607d0305094091146c0041c1c1e441c4c8103c800c10300061152404010b00e40310b029001c207055400c0041c050080564910346401686e0703459002079030003c80488096403c210303541c0b005001e60940815101c2000030300368240d00041c2c440c0d0200d01c4034454007080701010301a5109400e4400c502c1a4905120210f60500628038012981045e000d0403969034040103001000c01403145800c0020024049450142880340290001c0d1243e582042d010102180c4185008604607c0340165540c0f181c981d80d0b00c2c40d400c8120302c40f24001c0141c00c04500c80181021400d020002c01a041d91900c50603034440ca01081d082c260300b02440d003420154000d06c010310050780e2100c00c5039000030b818a03022400c105044000380c2202482d0005841d072000000d80092081c00119800b4040e641002042040b552080d2041c0f0507441002d512200c142e244100240e030410045001c4c0d03050a0042041c161b014039407181c400b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 403784478 1250 403783228 403783249
    0x150a0e0307060203060907080702101a090411010e03010c21110c0703031d010527030f0705011824120203130b0a0c020606040b01022113080303012102040209 69
    0xc0c2c1d0541c000080042d0360a01d868616042a81442c20480a20307200400949500d20801a0031680c4e0312a802040381230b4040d0005006100002c00700551401c003483d1101c5480b030700340056804684440c0c41c46005e85810320401207400019200c03000400e01c2000741d44100f1404100c107280d466500c010165400102ca400b4200105d64100100360443c03d604015200c07880c59035901011311510709a174080c9903801000d450260034030b84500420005480880c244610750218600d8240c8a040e4100ea02c8140005da140b044503002c0e2a802600e9101f0140c207600c541c2039005003604400340d02d10464178071188070a0b00f20764205c540740c24002100842ca02d4010380c0d00a494500f00800801c92400c140406510100d81000001104001c41d81d401c550103510303048000c103014800c030755446486840d640244401000ba20403602990490f030318060f003a00d415080720710000c0200350300c0000410000400000c8a068402c003038480c07600440ca00352060101005214101d030442e400340014680d0b80c030b64a0110703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 403785728 1250 403784478 403784483
    0x702011206060c0c0e19091103100c030c1107121505091506030a03021c02150f0106020606031603060911030d11010f180803040c0b040b030126150a0e0307 68
    0x4085529418a90312081031342d00801e0385c0300c200105204071200801c5d0410102e00e805200410981281c0c1061700c060200c60038620307014000c00761442000c41d12a404254111a161010044405628030854030170380040c880040315441407409001006d20310300540b02142c49011003c0114100c038000d030b01520000c0c2d0707503007032681e00c03180d800c50300d898400031501e40c400c4056001b00f0680036a038070025504c040d9016400c04404044100c00c030300520071300c280d0b5040320303c1440009c2a401e003450140c043c00303000d12883d0018090017011070914980030a0100c4c0d40601d0a40c4c59a6040c03c6465050052421080454000c05c003c510b030009034a00380451400f05116445400c1044040641c5900351200f4018210f4801c2c50041e443d1510103c44481101e100e820030300c42502c036981c40c50844074900706504030b01d85c0541c0215002480b20582c0340114181d0780c043d5520400b101c420030a00c52036440515180c80b80d43c002023100d10110f4580c9092550104003000049403600700461a00c0c2180c2c40003500b13 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 403786978 1250 403785728 403785737
    0x6080a0b0123150a030507032304020604150e040501080304080d052803050403200d14090307031202070f03120309020a05040f06030c0f030519050f061503161406070201120606 77
    0x8090542612070f066100d017140c10305018800008560100310542c450500300c0b901e20100128ac29522403605480107030600c0d01451644030040c0c0000b8040c0304440c01460310440c181000410700c8800442500d088403121402414480c0c0c40c1201940c0d143c100a550701351840b01c01d40280380082c65603603090f45c683c5443d20005054105418018200001c072038021522003240f5155550800c40043e0076145400f092030705a180c4220b00103006814411001d40d2940f52282d0344010003440084100c0310944529602240d185580d50b1000082d18501848003400c2c17000382c01e9040a0f864000c0d04407601480c801408807080c00c1c0c4400c0080c08803890a00848080d6030b80b26814420803400d070303944802400300700021a50341407540d9600707640c1d9a0f00c074501c0040103000d800c03041c0401904008401d210802c501c00d41e038a0f40b42401c00c0403d40044040e816110340706107291b0b4048140d2101c44803058640c64290368140d9025141400499406107070f0890400ca0b19449001c00c000b0b00d8410034019007065a00d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 403788228 1250 403786978 403786987
    0x2a06050106030e0106050a0b0d0f05010308031006020a020603061005090409030305010501140c07121403160209060d020907050901020a140c040e060903090d0206091807020106080a0b012315 83
    0xc00030219005800c00c0300d00f0303070300d400c109110030b42d00e08411000710740c0c0f0940c1c1c41d42d0f10f0807080c10080186c454030309010080307801c250010040080d03401c069481402e1000d429168203a40e110102d948558003c0b022b50083d4040000c01c1041c01e0480160003c0301c0c581c2040c92a00c017001c008282102d0b8680c000340c002a5503940140135541c0d100002044d02c2602e100402d0505411441207901c408035842200c09031903003544484100400084002d41244940e402d6984410451504186a11017001c089208880d44000110300703140c081040099107402802858441d03072001020351300c6030f00c1740c1c4915065105100405000031810185801c40c80800344c003928082c05040c0500055480c198040103003500560f04022220b0740010503158004c000301e8002071a0142030000c030310503100703c07d021600038030914a41000300000342000c501481880d402005182e070b440000d562175002ca00c00040040301404010014074642c40300441d15001480e1100030140c14060000e0301c8101480078041c51a000442e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 403789478 1250 403788228 403788239
    0x109020307050d020a0e07020a0206130609060302030f040b0403211a09042a03060507080f01080f120913060e09071d0103030f0212040f05030c0d0f032a060501 70
    0x700a40040c0001e5a920030f014040703030f000660800003806048202c850000000740150f1082220b00b90482d0023400c02c40d51010190b200400740c08ae81e004040108021500003d5114070034404c99110705604035111b10f141d219903507031031a22071018000b03804000850841c200130104806400d490b664071224005494101088109800c5090f0034400e446050000308200100e0104814036200c8559403445290f1a02c0081e415030740302c1c81d80d400c0a05428600b07000c0255042d004a0000e0141e070703c04500d1642070707913102c00c0603641d80f046551146041d04107000ca8841450f40001800041c04c008001240f10202c00181c003084500340c0e070000e400d50062105114002c8820310100c40508400c3d4002c2d01111502510204106010301c4000e041010465140c1b030728500c2480102e802d001c4220105541c0d07562044501a041541e0190910031b0140c405114071a181c220b0401020a41c480c0100241c14087d407416070b0000c0400710701503500b285c80c0101405c90b020400202c0380482c032031100011a0350501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 403790728 1250 403789478 403789483
    0xe1303020f0313121e0c170a050c061c02030403020102070b0a060f211b320d140114070906030c09181d010207122307060e0303040501090203 62
    0xe0009259030030402024020660f6105020140c40c04d038042078038103220300e181c51581707204070f000c00240403c200010b000421043c11800d204035143c00000e10214642c41001e2500d8141e007070307001440345d44200e50441481c1410030107017052605805007030682c80c0344050381d8000daa0003140c00b100141d50014000c0200415085a00d4004108400400a940c1400200c01040c060307030007003042c855024241d0051500403030743d0029070664010078498401c03062035851140c041482c040c40c61035040c210100d58024049003002c03100c0903401300c00b84904001d80418800300d1284510f00f030300c1d1109a0031800c24882c1c42400380644030401c1c0384d20f0108620b03000000600301c20087d0402d130201030600e0f4400c40c0f2194400040c10075900e140e8480080e0b00b000091481c018903a03080352114110351a101c2483c44072040d80030701299801886010311540015504803000b100e050101d101c1031951400154a0403c103001500070a4828040001d5640190305010b2941c3c200715002c941303981d124046c032411410107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 403791978 1250 403790728 403790743
    0xd090b070503090a020603040206071407081e06010e070c050a050307150501030206030619080d1806170a020a02210309011109010e040b2b0303061a07060b03070e130302 74
    0x40e071074024110b00301002c805495410419000c0d10590000c004a020b43d502c01c4211104150700c25003410b00f01482030390f01034450380c1c07510034034009020b242c4040d451640c5402d1140790510304400030344840d07800c080c0c0e00321740c05101078070320010025041d04090015008005191000740a407000356158030340b07480d0041c080c2c280e2611041c0c180e400c01e8010001038480c0804d0380d400110880d2072020400543c0104942501154008046886140300510342e481e080b882034001c00404d02a0302034003e445200c142c94540e0b1551300711000888000002d005240c00740d0260019000da0b20690300195071900ea6503000c0031032502d03041900040001880070800091140e402c3c00c440f41752085080c00041400600706480c0d1000c00f602075901e40c0c070405200e5891002895500c3d0006424071b21044000d140000054280c0000b20046441c2c0a004a0043c0749507400d28056426000000e2414115680b480007900c2040007031034143c030032140045451030410400510803005054000c610b080181802440d040e50f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 403793228 1250 403791978 403791991
    0x30b1503030c0304091503030e09150303030c0a110313030312020705010f020a020c03060103030f140403020a080a050f1c0507150515040b0105040f030206250c05010e090601020604110112020d090b 86
    0x46d101d004000190704100c07400c55401007120f2200d00d6580d00c2c1c10017025030718021000c0d075040c0400010010504404400b4102c40412580c4003204a901d8440d0140c0d244912488400b030903106403000c0000920a290302840d4054085003d41415001d0740c2d8282500c0e1030b002e0550359643c012941a0f070840d0b04001c40044000e003107008140729491900c02400c042640b0403001c0c10001e114642908804c0c50600711001140d025000e680038558490002e43c0310304081400f1180f5000c1d0320040d2006000000326441200d00f85a144410a10307012025140d03948030b100219031040080c0c010b80640b9445201d12441044030b0605e0440c526901420002103480050700035051140521080c000c0480903000c0307205880e41901d1940d0759240c4014001c09910302082c15141052800005800f00007017001448120341c0300b070300c900440c0c511940810200f00000c031101c40c010380c0500001004140d0003403080d0540003041c10504040408664108266031102c10780c000d60320749401e1b04100300a132204200e030f403004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 403794478 1250 403793228 403793261
    0x50f0703020304170d020405180406141026011d060702031c0e0a0c030305070611040e1603230f0105030c0109030f0c0906032105030907030b1503030c030409 69
    0x80d0640c0e5004c1d007a14542141c2c1001100403480c00101c40c07880d41141d000d040002c10301d2034000f68050000e1084c6a04031000c450a9013416080e805401038a03c03240d02500a81c01080240c6082040a000c031052040100001244900080980f28028031a5080090300c001a00a40712200c02485150110140401c001c641c0100302150304142034130112081024060310100718184000c4403035181560640003d00100c013540c10020800d50404010300c40240320395030600c00c45501d110102088c0c000c6101d999407041c01100010303440040001b85040e001140e0800140b490344aa12340305083c107608901c074540c884040e0a001d00e172000c08900c0c500400c400c5004020010007440020f00c0d0600c42e21000300100750f040140d43c10070141c074582501614107407808125869881c1800070714060034171000f07038031045020201040b585c410800ca81c828215400102070162665488101c00c4100a01c505609078483c001c200d0301d55018001800300031640c5000b91384032400c04070380708101c80049580d044140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 403795728 1250 403794478 403794481
    0x30b0c07021e03070303050c0f030f030a0b0105071104090203010609050c090a09110906130801020f0a08070905091b0919170705030d030513020a180f0e060610021002030a050f07030203 81
    0x660f40042d20b44240c0713a15207890f41d12841c0140d0b0203880c10001054009140c00042540c840c039031181000303584a26100c060a21000ca007280064400d8400d81030081d010985d041c42c03c8807036040c40c0d00300030340f0207101800000340039036160a0681120b5017603c0d241c01c81e4000103400000c3c2d1070048001006080c48260030090032035800c601c01c0c458825051810b004034008144c408000380d9a000e44130040c4113100c02507584408924000c01a40c1c41101c400e008180901d0101e12200d101d80c1a00c0103445015040c96001c0c0c6034400c80c4c00138101fa5043c19030041100f0015505140c581c500c010075416035032815420000d08104000e115542004e070084041d0b4811041000700d954009401e00240c5007901740008c540d04c5000c0078013010400c950b80072350840031001d4001149241c1100f10801d0500d149801c220124400280c001500d07515520540c1950241d001301e000c40c5010075074ac40a0300414011180030403180c8400b141a81c20449606404075980c03010480d03451081342c000360348540640b604500d107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 403796978 1250 403795728 403795789
    0x801050f030c18090f07060206011d060102060403050d180807170a0e0d0c05060a020a0b0a060303231c090204143904030501020d0b0a08030a03050709030b0c0702 71
    0x190980100840e940d5200700c40441d041c1c4c1c000784801070b010700100c8255054030b6200d0802940e2424280720780701c118200c0a161031400415150071750f024880c164064034550302c1c0d94508440340d401070003040307044c25907034400c044000c41980c80100a83e841102034135118401c504260031014100740c01c07150803840810410400e107900c0400c10542c0801181e52a101e040c090800012141c215000290031107000564050000c3c1c00080070b07038a4034801d0880700150b1341ea02190100340c6020744030081c04036000702018405810840c5140c44a140c030303685500d00b407108038400b06600c014042d655160503a039424201055007018043c100d00c2c03071031524070390713100703041c1108441800040441c2c0244043d01790b0302c030500342d900c10f00f070600e070502c19000f20b8944503601d90801d98000e5101d52a8200540c1c074211400340b840c07c02a807008212107040d00510304100e4a020140c015080003810301c8200003041a0200c0020000800140510240a8069250069841400f0760085c03040342c0c0303503036020301c9490b182075 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 403798228 1250 403796978 403796989
    0xa05071409031f242c0c0d0603020603010305010f051501141c05070c0c080a150c020708062d041205030901020d0603030e030105060a180c0203090a0e041a07020d05070305190801050f030c 82
    0x400c542c0700707081d0f242c0e44d0214080320341c000c08d4144c00080d8407000000000050001c15045112510400b4004000d5a00e86903801e801c550141010103020a110300c0c080701000080f4009810485540101e000c46601406900022600116120004504220211800e09c0780144600c8083d1242d0310082400c00740e40d4031102440f02824900070300c607640f55095104410301c00d02041004141d180220340d9507003001c83c0500e819a8408100c050702c0c05980b501c541c03c2d400f281d40800d02440e00028803803034080f242641121690f2008290176203a6408100d040c0480788203100d101c00441c000c0e664401070424400c10182994005042c0521400c81e1103400c1c0024421302c0300100303840610841c00103c1a80c10300d0140d0070342c0920020213601144420000071b0b0b5410b11503602d44181c0c4039000852442035210012000c51005941c50303030059200846880c1c00e1400f075070003404d00714000c0c14000e0501c3c240e081c60b41010501035001030002600305004208608000064291005040300680a840b81c900c0100e078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 403799478 1250 403798228 403798231
    0x19090b0a261e06041e0b151e130b011b211e03020306010e040504060f050106020d05190905090403030b0f030109020d0620030a05071409031f242c 64
    0x6081702030360840802c81003200315011044c51381c060400c82c0245070144c00181792494032004c0500402814946100d00d1000c000c0c00a00e40070024940365605c0004d42c5584001c0044000036814000b1100c0d00000180d8041d0041c9032041c8500014810002c4074441040302c0e00d5000120002d00c0319145140460b048111402c1c0d522104034070700181c8941d0380301c004843c0300030101c09894210f032030710051006001a07908003040200203c0020302450340d0300c140c12691010001000030010702c092200b03000e0b0340440010b02c0041074940c5801e582c2c0580300e20000d102c0d4802a90b0490200f80c0d1340c0000f0555051003001d0015040044000b00603044007600850210401814024a6075954035007000c680404d40c3c8070030090480156820742c407490b166405000524040c2c5418006c243c66010102c1c0802d440411145d4008014014008540a4583d414461b184482090b5101a191041d1074802c003641c2003034282d10300c1c8c6080b0400300d041c074128946401d003030f4200c802485284084000b007010a00d010029 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 403800728 1250 403799478 403799483
    0x8060102030a1206090213080601050603131410022107021f1e0c08150405100302012102160314030907050603071b03030603030e19090b0a261e0604 65
    0x41083c142400640c00040030660020351900c1d1010409082240418003008141d40940c021103000da40c0b5001001041e00007100c558100b83d2040c1d04020024080313501c1240030940000c201c030b00c1800046501801c0c2d030441d0007000b1202e04452401c800001c20501000e41100d4140003070701c071000700302000c2030021a5101d5084602c80e02d41ca9800c102c03819400c000f0042001e40c030010001e0000d0280d000380b01140949800e0103040c0c910b101500da503d0300d407090f54098924585e0301502285150300650b015039090b00c010001c01c1546408400c080c0c1c1e0b80c0000c001c0b1040c0d031822455981c02e07515001d400c011040f00403001d503660601c10041c0141000903418203503a02140c007280c903691100300844c0d41c4640795030f003210300d000d2521601c02059007542002c81603a11a0311023420703800020003440080c240d0500200b112a00c0006c081107020720503403110541d100090030b000a506e440d1b0b009200e2849000c0030a5108688420b840100007030700307211100f83c2148504444d8440d42c031b0b44002558405015101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 403801978 1250 403800728 403800737
    0x2011202070516030503190e06092205010b030709090e0d0c0503070c08031213020d060b010e04180303050606070506060603072d180e04080903010b090a090c0608060102030a 76
    0xc002488020820600501c004402c0030025607100d14109480703401c48101e0000c1031050300147c1c0c2e070f0749000e0051144c2021000c0c1525041c844090104501c0c900400a07400c80c490115031012003c042c1c5000341c0d03010700f61503180742d075480c00c1c0f201005141ca8082d510020000d89030400c445140c0c0340c04655107806d031081c1e1400924a0540d4140241107200d961401880010251000134582c0f40101c05403031554004050180695071f005540c03060901d9000f00254007030701700c801060001c2e04030780c04030031180e0041c94403020605071140841c2c11600300d8507079040b880051405a0042542c54040c2a034400700c00d644440c200800c0e80d031442e80d251005400c09128650110024001c14400c0c0081c1d52075201d0300d0105080c000015007580c0c404441002c010b000514481e20980d41003080703030400f1044594075110b00401e0394039500e540c2e0064114604440d0b065483e14050189907403102a4140182c5c13000100250014941c41c000f4402c0b88164070500030f0011000401c01181e801009a0f40b0381c8a42d03092 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 403803228 1250 403801978 403801987
    0xc090702072102151b120715050901150605040e180601030b130c03060519020a05090d05071203051b160e1003050f0a14010510030f060e030d0e1902011202 68
    0xf2601a4065602440000301084485e400e1031290001803600f2214000c2d40c014a02122900c3c1003440b40351005001031000045148109115034030881c0e02c840d80c00d0002800190681080c6e00e01c1d03d07142d0083e000104046800e119038225220000d8009110184402e03c20401c020f04a131034080500c80904142d20394000106182c000040943c0301076881641c41c10826140d1405c2401882d00741c803001c0c82d2119800f0402024403842c400c440c0c080b456a01d506043c01c0004e020814207082030481111207010301d81c1c000a80250b40f003c510000c5200307071191078440108105a00c0c80c1e485284010b12298030003203008460a4030820500103582c4804042ca8441d500c042c429109030320b01e44d100806908c40c070319102c004600081410845140b00b000c1411313004103459545400d071001580c0e03620100070f44807000c0000402005080caa554480e42022500fa090909600e00315003045650400c071f20386a01c481c0080304405d00400345940d00c01107030410b002c4000d4000070590b401c0c0321404055250f0014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 403804478 1250 403803228 403803233
    0xe0406122006070c180b0105090f0604030204020307030b150918041a010e090c0a080c0607050a0803010902130803031303050c0a0215070308010f0e0403200d020c0907020721 76
    0x181c41042440d015120503611500e601d010306103105a440381074144100c81a04d0038080480e80600020424142e40d0941004440000c00c100644905543c0307902c80300400c00040140c884c1e0010758441d205944000440c4201101072088002d40e1000b00301d4585820000c2c010300d5526100c42152646c40c200107900705654503d0000d00c854801044269220b4003540005090080b0685a52145459505843c500c010820074003000032041c0c00703203000300c0e049201c03e088142428005020303824003034801c90300720b00010307100c0b803403254402e07000802419000100e08405030000380c611802010f14400442c6140381c02c44601004060a45e001002c01ca40051403003c45c0108000d29515142c00824854081700300b560341042c1ea030300c0004210040ba400f80300014110b180d40c50741d07000b00e500b204455a600d984070359049802c0d1502c24840c8c551006101d0842204580410044100d442c1c160000c04103c404c00341040880b1400400351000c43d072150200b40a640002d0740300b190480b160440484440c0b5051 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 403805728 1250 403804478 403804523
    0x9060c0308160302160c08070603090506010e0c12010609031703010308091002250e0109020705030d0207061b080406240612090803130c05040603080a0c0606240e040612 74
    0x1482e105c824008600b19030700740311904100001311a500c00495003010b0751044250305a4400080140c02c9810000040007413181c2c0e1582a90b000a01102c01031509103458851300e0020002c1c2c01850005900e85070038070400018042000062a80d40d04103030a661555071480d800d0311842c40c0306800f4050012141010030300811140108103007031640075035101d02c43c01103015450154402c1a0480c456403000240c062440d20882d2552a040005940781080f401180000303907200b0f41c4110ba102d13a4911001095951a40b113030b0351254002e0b92020218282070802c0e070140d84078a041c040c407400c021880840c1c80241031805000316101070a080054500c2001e0a00c0107120b5554041c0c01d03010004208040007420312500c2908620030680d551074551a6024401141d1582c04001e040703410801c841814503000e040c20800c0d140c403078003004c1641a114498a0b0380003480074001c020b110906500d0070010340c0c224003010796183c015241040300070310b007110300c00c0c03001c684000140103103950803260306502e0380c20f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 403806978 1250 403805728 403805737
    0x15010309052a03011a18100302040c170a0b011e0504081624020a020f0f10050322020913080d020f0d110703140a03090b0f0709060c0308160302 63
    0x403103035007412028080091644001c2c0008031070b220b5403030300d00c03003d6001104184504400c171002e4001841d0803007440c540c40030024080c0c0040000c46000c0c10000050740c440c090b0b10b0805406a0340c00c0c0202c40b81892132400703094041c01410000b130801d031182c55a40d9019000e50b440030426503160b84036201140080c0ca86d44038542001401c0c0c0511403100c0440d8600c0614a000c071054000303445628004140032003254203c0354541c0006030407407030721100545424641841c000100074641501d03d00310000060300d03c141940030b0004500003004110201078103551100d19070800e40f451841265031035000400f81c00c0014070303041000b01e095081d881403010403020354410040f00c400441d500c100f01031055880b5040070040d40c1003241851041030780001c0c2003080d038180039810f8407100c1d404100c0d41840c1c0b0032904082071900070540c0c0c070f440c510041001c2c0f000903401136261404060b2142450342d40100300e807030240c1000f02402514854140044d60203c24150b100c1000003000c03a1020080004501a04c50b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 403808228 1250 403806978 403807003
    0x8060f0405360c030d0f030506040e0604120806030a0312090302010e06040c052d01030b0f152502011205092b030f18020f03010f09150507081501030905 67
    0x6880401d8010342141040c0b9008400034030301110100c102c00800c05545041213180b05e000140765850700407286009400640d0010700042012440c01024060349290280c102d805850394401e42d5502800d06820501d4142c0213441900a011003000e144c13006004400c1e102c01401440d560ba1040c18149071003036210100c0c00580740107599890500341080d90b51903900c3e01030369100b42145900418030800c01394568500b1400c0060358402e407102000190001d1404100040d00200360844200d03d0303a5950301540801300418001a468518500c50b15684100c801014203041c100010020050b03030700805441c3c1c54205c0303554007060903a40ea814071401d01e46100303072014002c0214900e22950b800781502d140d80d6804a65000c02c600441c2c02092825550362041200e0507030400742800000d1b092481d054208280d0160002c20307400301d108045001c03508006026039012280105010880b0b03914000c4c1d503009031071482c100c3d901e41071024181808000e101d1495040c103a42d07000100405c5000d011415500c3c0313 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 403809478 1250 403808228 403808281
    0x1104060806070507030806060412110d050d050703180501090b0c07150806010f0305011415120108010921141602041514420c03071208060f0405 63
    0xc040c82c000d0b02e150064501100400d801000040040c02e01d1000d5908035144110f100d24048410380320b00900b81c0c490000c090b0084403200c80f40c001b2410400c448400c541e6195203450352080c04e800e0081140015041100c81c04202207010413941e0307801000001524406985580d84042c400d607001d03d443c440741c0c05041c00c9180351940e030005a0308001180d00c54082a02c88200f40c01c0c48140880840310240201c005140041c8980505c5041c1403c44581161031020f00c20720741130308084141d4002c070090b802040240c0d1500c1008003040142c45600310350010450b100480c0d80c4000d040279201a11420714001150804a11002c410192444200002d038003d0305c20400e54400c00d045c150403458902a40c030080c01c0c0f00010242c181001c200012000d200c0700c5012918545050007008081420204001140301c041c495580041900000b00000300603035006680d5a000c0c0e140034444001d04080c0710381440402804c1040c0b6860380404188845070803200041c5640d507016200f5054000c605402030140b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 403810728 1250 403809478 403809481
    0x15150910170f2d0118171e03013206070204020d09030903020a083f040807080601060c050309010c0c0f08030706060e070c031b02120309090901060b071104060806 71
    0x50340d146116080c0c0084502043d0900b900208400c0e09881000c0c10780b05290148542c00b5010800000c0700d50701d04151603400c28a8106030070306940e40c030484104805407400000004001038440043c11620040c0c4492003200c4800d2001c5480c0c1e903030024030120600404000810008540d20b40c5d0490b4900700703005400300000c5041e07003001001c806541c00101d01444061902107504070340010f0041c107100908000103442141200d003c000514a000f020b01c10118295080c682c06083c0e82c06030000d4001c00c030007040d00c58a808601407620f64184c1c440070a000001e900200802c40200860b10205002e0900400d05807c07881c041c4440d2840317500c1b180c5181008040480c69a6012008001c01030140d8002d00c61a522801038407103142095a010340858060720550001034080d10145c10170b2860300d000130410034599004260400d2812144e91141d41001030403100c24682040015007005480000300030060501d039210340180300d821070141540c1e0b014545508260790b140c1114001c3d0a14a0956807a07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 403811978 1250 403810728 403810753
    0x70903120c0c030b0703090c0602071a1605010504050f01060905010b0d0504142505090c07140a050105130303150302010504140a0504060e011517010603050705070515150910170f 78
    0x401e0261012100710000c00d2300061103a100145c0301e0107851a00c1910701d5041c1042203000026446140b03002400c4031900c480001081c0203104543c81940141c000e0411f000c1007401080c210342058020302d04a620385001800b078150b80c6402d50742403036031800c2c0c0007c07640c070340d420a0306110202d0a2400f403140320765444c601da107101054440001c004003950b0f42036216284c508021014204031a009411141445a003011400f80240c007201b810500d402d4502d09000c50300e9050941c0c03412100e82990a00070b080760010543c0c10300c40e05100000c0e0403501035202d030441e80020b04501c258414241007032120090f981542c2d0f181990540101401402003000998a04041c0d11520b002d200303004200d0603004060000d01d003e400b40050180d00c1080c0014160b003055015001400061b000c1e10401405110320300009004004114100800240a88242c0350040d21040c00301c0003403081038055030252040c00640203903c008082902c0c3c1c1400e08044081c1f0103803609140200950355500701d0721503003120a48 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 403813228 1250 403811978 403811981
    0x50103050c0a0608250c080d0203041a090a0605060109080609010501031e030f03051009090b0612030c06040b060105130b040509060402090f040b0f03030a1205070903120c0c030b0703 80
    0x50500705a9001c1c91071a580c100680c1e0111044640080b03581d00c0b0300c00654402000d8480d100400d402c2d0030320700348004039902c402049800c0011010160b65002047c0b1043c010603512042e5104403100c42480d603403805100035921202035880003072103941c4032004115507a0044c00400c016140a00484c0e44900c1c01d1900315010700820712041c1c50714416100e06161702d0500001d017011554260303c0b505914480e54a046005086c01000c3e00c0c61300500600224914099008444245002d40c41d0881d246c241141000701d810320100800c0d82c243d0082010041301800420300513406600402c180b40c0e00d50b113250068a0521900809111683c102800480c140d490400500140c52040d90040d0243d550001440101d10a080c107260313110a041403010200d1030903420800140b400601182c0706e24080d030004c40d10f0754101c9003224001c198040c4840d01900010f21501e50b010000d031405890461450f2555103603d21400900b508020b0049030010030300002103525030003503030f0040301c24040307251200d8002c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 403814478 1250 403813228 403813243
    0xd0e0f21030c0f03031e13080f130303030902090705041a09030a0b1314030909012d0801020a14120c030702010e03070c060f0309051e010e01090825030518120105010305 74
    0x8254680c0c06c03948a060101c808004c03445103a00c514081c00d038488a403a040341503005003858000707055040290405070b42c05462141c0040d8401d80703001c038886020b131040080d4104020080340400c0000e110400c241b190685000c0c5225220782c1420340d1fa0581200404e003070614450000d0500b010071414008070411001170020303968016148034080013400170800d501c034810f404589a20440102c0107200c0030103108100c0b542c400402c002c0903a90441d041e4880706441469100c4030050354042030322041250001071400f9058610f0000c5841c16075541e60380d4501210181500210f8180403002400700f034000d40c00040c46144460450307841d0541454940b40c0b41d9030502860b80050340040d5040c2a00d4001d00034000c0f4954801c000c0c0c0704404010707007200724011009158110719900c858902c18200420320403c1d501d58002e1050699980c400440c0340a5045041503850101c01442040c201290b480710984800440060911051445850000d4068140042c070494a9480c0c000000308100b00003650340c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 403815728 1250 403814478 403814491
    0x150103060c3e060c03090d0323070201140a2c0304030609030c06050c07020f01051204060b060f040305060f01081507080402040f020a090801050a0b0a1a13080d0e0f21030c0f0303 78
    0x4071001d00047c08210180c581003144a0036400c0d03440e049002c2048180d0000d0340c8054280b00020703c0200d154401700081406480d041d200b169504814601e084408141c031113600c1101c441c00104400c00c2041036a80d2143e48001342103240e0320b4081a040500c0f44061940711a0040401d0009051a4000c22826401a00203d1060320f070003400c2c00b11540558156943c4440702c0c40404099502c9441e6000a0703c2c601ca91075510007410020f501414840b800074001450040d0000c1c0010310300384c0c001424684042e04214000d0340002c0070600524100c0c510141e000e2010725000c040e90f196440410007a10301c03580c040341c0706400419004c102952018940b42150300700d400a0010b034940c00365000458a80940d91900b025103441300307120b189010a841c401c1940da1034202441c1c02480130026101860b00c1e0000105500820b207040e03021a4480840f12189100f26040850009100c000407041028012035070300a6420002d12180007005006a424038194003041c0c42e25001e200c1c04164403580111440c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 403816978 1250 403815728 403815733
    0x3161707020f060a0b13050603030405060c0304091a09150a03080a0201020702010e060313020603063706090f1502013e030408090111030408150103060c3e060c0309 72
    0x1a1000710136000300504050040c1c440c011056241e1004e0029010003450107400d44802c110000d115150a00103000c0c1c600000040c42c0c86600701506102919008003103008540107142c220501a52080c41d421b400070b200f091403c010a100134041a0001981d5001400403100883c400e20082e40640003805041c1c801d07600d60742c1d48103410040261303500042d0303980364401c0e01402108005040490043d0f4020f84020142c0ca085804e561108030300c48910305921140c40c0700d004211740d489416030091000352565003841000c45003041c0c028120245e8511501403200746622000d120a8001e43c0301c21886e0380c070f0f444440031000039445081012007010300e04280310780c0c80210824100c1250405c0e0390040f68001d041c107150840c01c500440700f200c03031010300d9401070008000001b244a420004842964019201e0501961541c14100c084030405c40c40d1500f448002c24602080300e907160071124240100c466503c0107182c01d06981900b601040120002c1c0307114000c2848280b8801101851040101004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 403818228 1250 403816978 403816981
    0x50f100f09120807050f0f1c0201090f0501020703091a090f010c02040c08060a0b04120305030606040e15010e0d0b0708130605090319180911160b04020f030d020303161707020f06 78
    0x2840b50b6a00103102c7c585000d0b08001100d11180c148103030310030b2a03400288004556400345807141481100c0141c0708a034aa1b500082d650201a04149080c0003040c0a084102d00c0300040400f594807840350321145171149400c4146130b4a507078024920070485030340103001004a0b0f200b20303c0182c418071043e62194400e02ca591800036800303142000f00c5064813441c000c034281c01c8240e540c00340d5440d0005011940c0c414818000403c01844050407141b0524210311030500d4403201000140c186a106c090a500a102c41041c03140480c0300c550700075070003000c1458151a2550750800300e000c00b03101628014480c0c0e0420b42408400080000074018505070014210300c84081c2e11016a03840311210569402c500d03c0300340400414141d60b00045082100e50300061400300c09001050b00503d0b0150215a4804100300b80400e5040c10385c2185070184040d401881c070400400c03c0690b9901000f01042941c03006915801915072140d580c80342c084449030f003007140c10300b0059006900e680340c541104095211703c50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 403819478 1250 403818228 403818253
    0x2120f01050604030819110d0c03090905011202220f0e070f03050618030f04030f0c08070612021602031e01050a180f0201090503030a0513050f100f0912080705 70
    0x10448013140c0e40000b98a2800701c291180383c8141c0141d94045040c4400c0c650306850081091110f0481030030941d80f890b40d13603501498040e203845640d4000040b12840c01c40148000d0b0325615100b5074840e0111904075428144588012108061483c00c0301c2103070503c7c84402004045400a0308055a00800d481031140c03a5501d4580d01000c520024005500240100d0760003001144620255032201c401e503440d0101204440300c4581c0203900c22518104140030b00d105003e040161900070b1308007803010b05002e81c540003000301881b1080e616031a0482d030004011080d0303400d01c2150070040f9405000e80ea40a040c06401340300050b0003100003a245d500344000150341c2d403814403914100d0309528031002e0060031070b519080703900a400c0c08120705000c00620081040da404001500d10365400e99245c907030f10904480801c4800c040da40c0700d43d01820400441c09c03c0d07030303031900d00034200c040240c030b03202c19084c20440782240d01c203941ea804540003482c07082c5984107100c41c80c2e008008480c003074001c4844210018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 403820728 1250 403819478 403819489
    0x204080d080a0b0102030910020a3003060b040b0904090c060503011a040f1517090f010c0806030c04020f070c030807030e031b150d1a0f06041d0a060902120f0105 71
    0x1030640f0740c01030300f080001020520340f004248440a02a1045030780100a5079109440c5600014a4203800d40180725241542e80ca00104510142003910b8140000c42c90240c41c0c00d01c60003240511a0040070200c0d10300015121036100c2c09085401030f4460b404a5512040508198028041c2801000c022015446103904203400c0b41e04495031210700010503171800c1600405521480582e00c00c11075011000007500c0c0400403100c0c0140700c034801030000c100034540c246003101c6200800f01c052100003002c200a950f408140c01c00543c82c1a00c0269036402c417105020124499010001d10215000c07038003000340b18011018043c001e110b41c407058405410b80c403c01d6070350040030540341c00300249102e1600a80c10500d0410500c100c03d0782c2624200303458003501d40300ba26480f2104026109071460b1048041c40c1100340041092010356426140906189070b50340e03607103a82062240c0480300c0c41c000c59034000c05a44580c0013080480c40c00c5403100110913000904034020b58030462040b00d070100104541c0f401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 403821978 1250 403820728 403820741
    0xd051f03050c010e01050c060403110c031b040203041a0c030415090b15030304080106060c06060f0f03170d1103041202010605012a0b04030f111c03050a0f0204080d080a 74
    0x1c6001450107811030780045400f40b901c08001410058144035000104c0d00030411346000b548030380c032609255024500846e00d4000490350700d610981c40482100c5c01e0b070001380c000308002e2105840c05030b80c03541c4509014040d0110180c56650940c281ca08005061440d80d000e14040d034070401691012603c00d45001054544505014051030500300110340d000101280c0d0300314944010f001c1da82055501c103610340c21915140d0201000c01d106440440401095200d00c03c054032095000d004447d0800101001c40132032404000d1190391081031003400100510140e0b114040903d9042c002c6002c0d24800344510342060714100e440318110304624000f00d00600a007002d80742d069540014a1000314100b0040d10005d2411684005604940c5000308050440c0380d44200c3c002d40b0348409031100020024082041c0c04940700d901e403c0540f2880305c1940341654241000140d203030104030740d00d0314a0014002e02102e41340c40584c2d0310000b00051000b801081203241e002d075a8036420f44550350720b41410144c600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 403823228 1250 403821978 403821983
    0x303041a07030c06061d0a091e06090813090b030601051309020a0801020d020306010908060103050a12050c0d030c0e180f04080f070302070906120203061602120d051f03 74
    0x14480d1420a444540c50240c10118042e00d00089039442a454250484030780340c01c034000d407000c00008442441c1000c3e508076044864010200940011a2591411300400764008020a081d21002d00c040c480306402c25104c41e6001954903030f8030170200c4020155500c01e407003402000c03820900701c40c000b8600400d0050407550090084586529140c4d2024018400d12600700e900089184000c58407000034400f800000f6a000001a43d034100740002600444050b031024800d03901c104018000210045000151140d220b0442c800d41c807980c000948041c021303090900090701c07400601c00c10305940354004600200041d00c5e0f10111a032800180000b075444421280c3c009140c0c0004200c0505030400c0c510b81c01801800001d0800c0c0e04078034500c00c0c03030f4082c24080c0c0050f442540c00b4480c0f10964403e643c01042e00c3c2106001300ca14a43c0070079160280200b22000384100ca82000129500038411440c17018110009155104540d0301504000c0c0000e46030007102816100c801c0b443d10f803e820500042da42c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 403824478 1250 403823228 403823249
    0x140906120d080604020f131d07050403060b01120e060a11090d0206090604050307090212072a17040e0a0c02010204060c0b070e060d0e0114270f2505030304 68
    0x3000954150b44904029003c00e41080e03081010b1160080644044d2802c1404900c03000501c0c1c4c03410303981e1003001600f000d44807502502c10041c884120340200c222011207a10110105120301e0600043c1c50510b540ea400c0d58941d8246660308080610108485106d5a2510303800c200000340000355100f00e002d07240c1d07166000a034a034410b50140c90101d004d4000e100005142c585040d844001280c00c1000b00e41c0038480554011408004450104501907804081d515006403020ac26214030660303a13007204c100d55510000b070108a000c1c0000007110250403001c6520890f41d4503130b984607003c1034200440b0004c0b2064680265010712034418003c4808aa0b09a5102c2400c02d0070f80e00e41d50800c035000307000030051104da121030039855226103018122100c01004009404100c07800f01e9402c4d540404490385084c01c0c0102000142d491120040c030b48000743c1c840c0901c0641036143e0040c0782085203002c52400c0d01c641032030000d10810f100000054060004c0103850681d03544c07014035540340618000c04a981 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 403825728 1250 403824478 403824493
    0x4050925032c12040f030309060c0c05120106091107020f0d0221030c07030807030305060d08030a0f091e0210022b05070c0e0106170402090c2214090612 67
    0x200000000210941c1042c41038506580b5000404a0b05501030362103074402160060f4204145038001c9000c03401040d06051100c1200c1042d964199507115038041c180c49491a11000541810254004070140001c120104165030100c0c0d1031031060342242c502280b181c0600381c0c484d0001e0074038801c0c10f00c00c942c0c041c01403606075814045401c4030403121500c0003950720050040250041d4208003100c000c0d4054584580c0e681490704004080e110001c0845001d68410740300c2000203041542145e51002000100107407040484074000080d1803043e4010b0000c0783c0070f4038074a428034507101d0041c0c2c105108580b04144412408816a2a169115105900d00040606003552525061400d0004206507d0110314216555844d110071308625005125102c00700c3c030060003202c1d00010400c000d020301c01030a5415242030f6000408003a001001e0103021003010450340c000311901480010b8130b00c4c24051a024198458007010701c91071f46000c00c1c5104590440102d03d0609202500707081444105010309002c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 403826978 1250 403825728 403825781
    0x6080718061a0304080c06040305070c0e06090403050f0702060706060504060e0702030702040b0406180e010b041116020604050d080a081825080f160801020424050405092503 76
    0x1600000c4c81690640310800400e8407000f82444032a1003503200b91102070b12400503080c400e85901440d08402895100342007800340541c1c40054040c3d0095261803c6680c4aaa51030103042902071220002c0d045000414140100076483e041441614001c0d181041181c0d600d028030782c80507505803005c40c003613001009460050f04207504940c1c00c01801802c003040e4556111030141681c201c884000741125038a02000c220383c82d003030158201840c8101e40500284d0807481e0400418801c2d01c00141710f02a205c641c0d1001c54803550161402407400400d4401d0300007550408401561011240400203032000e00003506188841030500000e60b8003a0080c491684020f0b100100b070b082004480c1d620150807000019032000401c0491489a122406060246c0c0f40c0d40052000080c1504505000d90060205004d1524001c0413840c608a6a1301c4400600210791b00c04e8909100c0c07500260740019415040100d508040c02000c051040881c403010f130a0b2804d941e00300d045860b080356124a110880f071000c0d80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 403828228 1250 403826978 403827029
    0x3110d020f07080c01051609050609041d2a030a0314030403230903010605060a05030f10031203021903060803040b0702120114040b010b0418050a09060608071806 71
    0x2089409100d88618101c2d0944030300ea1a40c0082403480084da445904010501c00b0305e0301c21184031660741c01c244c02c1c6a0b0034000041d6403405024940c60241c1d41d2440c40141104044161100324440841034032403000c10014843e80c40c00c8500002e00c0c030014103000130341c0c19003000180c01c8440c68259079545031808490654210039030000d4020341c200000c0009010111a4901880d202003404801071035860f180c40c0700b45800c0d00c1e00e90380328500c2001b0a02601d58031340d0704681280e5010070301d1864000c41c0c0d51501c03200e0740e8a10302c0e504045c00401c0840d044031111034060b8010249441450010054001e00000407000e5810074025046140c00034041001049000400390000a00c010258201d940381060b01c20b0840f00c840d0140c20b000345102c400d100a015000000d240985059155145002c1c02c0c410384001c17400c0410b040e941c115a4540015451039855030228505070384c40b42e424020580d86082c81503448621303000e180483c485e01e0300c40c9904425144160f000b2241140c0c4044074540c0743d2062032a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 403829478 1250 403828228 403828237
    0x3140d09030f0203010e07140a0801050903070620030a060303030b031c03110f03150a080f0d080c090405070801060905241608040303111e15090304150309020f0103110d02 75
    0x781c056484005d100038441040c4008009401123105856654407950304211040402d0350002540e40d02d090107000d60540d000c0211100d20350014030105040c21039900301d40c0060280c3c1000c0e145c0aa01106028075041301d03800040480380030780d6041c040f5140e25001c16407210040810060751903144484412058040e400100020001001040c00c0c034030324441001c8681c0c821102e00e019588180c898480d546008602c5401405000b0010b00d4032036080e400b440d81d1840d1100420090103c00d400140340d5a88407002ca07617034001e01030400d1080b8103140707030b015000c0b52003130040402044807488041814240240c9600600786a80140020700550356844001c40c2e0002c0301310422001e44102c0d001c04a0300784001000218401c1c6d440004002c442003019080c084c1240aa00e030310100000d061544400c0011075001c0c1d41110000d5000d1500d40c2804c0c545140b10329404000000c529a0707900860a806601c041c88207030003942d00e042c00c0f401c800c00440071103010b0089240e0000040c01220010310f01c40e40a40b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 403830728 1250 403829478 403829483
    0x402090f0108031611030307080c0709060f09020c030409020a1107060206160305060a03060204080d092310030e06011d090d0203041806081b040b030105061003020c010b041503140d09030f 82
    0x80801740c000b60210b8159442500241c809807000503086003100000c0115100800701c488040040c1d600780128014400d44600c07651264075008261150740785814400c81d0300400010400715030301c441440000e0b03d074880406d40c0c01c1d40e50084583c0080c1c1103002054031480f82030905103290142299172025001094050700c0590040c062030004000100a40300401c0031740f800400506d44107006000c02081d0744100d8000507411403a14a41b68454166540c080a424400300d50152420a4024046005041e000c810500da8801c2c03000010b05804841d40d03c1c1d240e42e00c54404109503641c0c020303415035160342c072808480050340204005c1281c0c0d4281540e480c4101c258a0022805581d10310f60f940c075214054285948040710711040c0d414501d41441080044a0158024441d0b8688100000c07540040321000c101819000524000410402e40c8540074501008100704060a100d00301c000000300980022502082d1a0003040c507404000140308080381c1607561450502c83c00c5607071b1440c6034800b00a08 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 403831978 1250 403830728 403830743
    0x21c1509050c100503041707050c0111030913050a0b03030f070318090908030f01140f060307090806011d0c03090a11060c01020c0c01021c090302270c030402090f01080316 75
    0x941050340e4040e5820090f068030760301d458403403c1a0606000030300744040d01800c4190304110300f100140300800d0492300644242000b60740c1c007880c140301906500c0703640025948420301a2a0016554007507101c603002e000d040c08108168045103060580da481015588130920b2414440303000064442c0c98159079111178441c0032043d80d0350345c08014061b20a5400b08a400503030120410440d2101d985d001d90041848070380548104101c900810380101e41d115103d401502c002000800345401849180028040704045501d0b41da55055480d2106100c1c0301305911040d50310f0b010400004015050728011001480031f004602d4140c0d450b10740f41648110503030342040e0107000c0b903840c1400a10107004090480000b901c0e10b000c89100081c01c16003a82200d588120f07944000001c0b1940c4070b54040b041e60350640341c4050200d1441c5040c6240c00320448035003664050102000f031000b03100809580558403d03100b00f11107458103081181a004240a00c00c0c080e4818010322070b1034400d0411071900180150036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 403833228 1250 403831978 403831993
    0x81603061a0f2709150c0327070807060305091e190237050102070b1204150207050304060e03032115090705070b0a0b102a0609021c150905 61
    0x280000701c0e09048990780c400b90002c03c5006070542142075071725407202003000319510314603020480f00c0c08803d0b1040060003e4445003c0030310b440804110807405071480c0b0702110169079551500a015240c21103c162141c052030006ca0340c0c1141166180894070002c10241602261031098500c50310102182030342d02484d14100c4a080b08040e02c0440404514480101c0460000340c03002007040c40d641d032009046510032007041000114807400e90700d0700d0440200e000c2703180c3c859007015010780320780001000c4810301c001401e10401c41c0020013001255081d48440710a4021031040507240c1c0582c0313000700a8040d4200b00f1a190111220615038440c3c038120400000c1c112140200b0794020003182c000b0040344c0006140814810305224095007d809880240803503100040460310440c00700390001c090188402d0001e9245d85c98400c0002d00540700d06001004211030305001c400350000e5202603000d0685881d020303202c2e01c4494070b028180b94019103210c5031071803034441e00e00040074203070401d90700c2c1e00407282c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 403834478 1250 403833228 403833289
    0x21602060a022406030105060f030309100c1b180902030705010c14010e0d02010e0703020f0603041a0a091202030306090105060912073302070519081603061a0f 70
    0x1243c1c01c45404099042d10700b616140c000d0508585000d8050f5100b540b503240c11642e0303660008111101e0030020780b4680300d603e41c03009060b5075603a40340c41e005025489041807540c1650042da60f5008440e2102000d03000502c5030008001110150724002c1d401d41c01040081c481035010b610703540003107071051380c0c01c1c0c514008006105003103821100c05d140d80c541055625080041d0b09020b240c03003104010024280c1c45203550700080340c00840d9480c403030040d58007100140520900120614080c191120103440c11314250114200502c500803045500b10440d0720880301d402c2c400000c0e00d01c2100301500640c80d0f039017408108503840d0803610f001503102c1901d9030402d0856606218500c001c10102100b002e8030080c01103010919400080e0011200d0500501054442e07400509141110010b86443d4010000300c071028921140c00d0700106c549129015400c000a03014a03810403c4a01031031041044a18001c00000d400d03065504155002d82a810700c0740442c40e2000070101d00c2d0840300e845844d02036510 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 403835728 1250 403834478 403834513
    0x120509041d0c1c060902030f0a111005030108030a030b130603080706180201020604080f040f0e0f07080114040b031c110715080a02090a081e0f01021602060a02 70
    0x20411540e80300c804442024041c1010020034800714002c03150380400700040290700e0380c101c0039403001501031501c03003070160190748091100001015552068030600d008030b04207040000450642540202100303030626000038810800d99051b0781d002c0c2e020714606800c114048000e48400b69032181d02c10926400d0500e118030a11405005601c698043c54075030040317040440440d00030121800080900d0303100e201c0180c4c0d011480c00d91290340038905035160280301a00030030301d01450b08191030003030304e135100420140d00a80c585807080000c001481115560210220790035a403c3c8a0340049140d101c2851640346080e030440d40d1329550140c01c1303031603010f0200408005107001034180000305468910540501106000c4074010b040200752104003007612000c01064254002c107001082c0344d0119801960b83e8410a0040c01429500121000c001030319003045092000d240105120784210078070709910701818001e89421402c01041142526a16001c0c421075a200c50001d0046000e0314200700c0b160f0b0007c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 403836978 1250 403835728 403835741
    0xa0504200c010606020601080a0b04080a050d0513060c110d0c03140a0f121802090a09020307031103011d0709050702100c030b15070f08090d08030c07170a0c12050904 73
    0x9000003c1905841c00348041c0c1081410380041641d90800b40f03003071000c90034a4801c00e8016504c0402281c0e240d0320440226503900a40c820080034504100034009984c01c0c0d041d00d002e9941c01080100008a08042c1c00d440c2021001032049140c0c0002290345d100500462400303e00314001e041c0b08802842540d41e28003581d02c161004404074000514071031305541d203d040a454540c10320300030095100410342501030b40d00e08420080c4034004640000e0000c2e81160021507080d036025003211461500c9242c101422624540454002d41c0ba024104034007181203400d0100c4000c0354006440b880c0e041c4441781c8080c200040140c02944191000c14405804501c5040d800403110740e030008883c1e1020041106644010940c400d4019080c40303280003140d0b12080341e02030668807801295a0300c101201051b041031110070040c080c0711011041048100c080002800303005e201e4864484102000400c269841c0103040c000400110121003a000055181d54a00464195030070407a0a1141e6040040c040e11f11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 403838228 1250 403836978 403836997
    0x120a17100815040c050f011b0f0303051501050d150302030d0810060504060806040c12060b1806070b130516080a060b03030901020a06180614010f140a050420 69
    0x340842040640ca060051102001031000b0a00d01c0c2e080a03150380000710780600038030348a022410351071001c0d68000d98401c1c1030742c4608500584003162606044524480103001540407a04060005625840300141c410403032105031225803c10040620450040031194203460f903203d50790f01c020001da5002c100031344640c88070355542c111a10784899038001d4142281d01c0309041c04818041800000e41024005030b00401c1594001b50100e498076088624034118a0824800d618120707010030081d091a009243d80940044146643d00246040c00203902c030300c1c400506080c2035030000c542d00403000441e506c6858000c40c00c640380e801d901c0301a0490a00140d20244a51303101d40c644500f04442c9003c1c10a5480085001c1d60500e0319030b500203515154021001480c0035980c00450307446150780254610720b00d801607805c01c11071007020090484084207000308048005502e00001b10100a02d0341d904035500c002e44007aa20620f0310b001e00c000341550448200c01050541c844d40c10050303502e40901070a00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 403839478 1250 403838228 403838251
    0x7140c28080f040303140414010c030207090213080c27041b1716050a1205070f1d0901061208371115010b13080102040617010e09120a17 60
    0x1132031841c020380300106540d041800c80006200801c000640f00210718001c13002824040315800d100c0c5000c074100b40054100a01c5240302188102800f05540c01c40b40940e610355003181c443c8210038080010001e5080010400c004c0c0309440081c11440c007491841c1c00500c10410b09048240c5142264100b410756005542c6904813040010000102005110008050200712402e428280804501c48103218024540c0302e040310030301e5100b000000c1100100034045003135031044841d1a40d203000b0403000040035142640e40a41d001c42d100c0c00041c4105012a50006c450010302c503841c1d600e00c001904001003801c1c5994940c03401491640100c86c0030800454011103001640300d80c1c0002600401201c0ca030b03030106500943c50b07a0f00c0740d0510307480c9605481455484a890380f003040c2c009650050180c000150300c0d40040740c0010700c3c6400a9962146101c00b4511502503070b00e441c4c001d00500001c890400240d4000d0b04508000c46c40a4000d04002d201450003101e90010006003035030b20081a224200c540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 403840728 1250 403839478 403839487
    0xe01060215060d020f01080c07020d05030705150112021c020402030a1d0c0d08090a05030d020604030f050c0c04050406060506040b07170306030a110102101407140c28080f 75
    0x1c81c079203a07440d602400443e0420f45819060300815050300e404071a2506125141000c85c42015000d020784589641c018000b00340480d4516043da00c0340c0280f00704aa841c0b2510a0125014824007032072410b031202100c00100c1d100f40c680070882c6400c00d5481e1314a244541d9400b80c00561205d000540c440c941d02171020030700c61b0410001401e480d00804050700e1a802c100d040b0500c1b540c503801d44807401c0342c003d4200c0e80c5898a07500010804515940010340c10300c9500c401c040140d401151b038520950094542100e0251149010398080c859001c850a07190405122908140707080c2e1b0050360441d00030ba0300061425141c0b0003048090384190405000300101080180821115180e4002070583e000301c51410743c00e161010960394242c0b50306c0204620504040700c80e540e4402c001140c0700c004818170500c0300170b040566102c12120250350b21400904c02c42150004407214008a8090220314802020001d84001e03d55408003250b22120031102045c0b844034020903055406020260840ca90003a542c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 403841978 1250 403840728 403840753
    0xd020c0705062106060d0e1c1403010302090703060e070203070c0b0a0e0d1406040305040501020f060f0109180501060f0618080a03111f050118060e0106050a090e010602 74
    0x4000c001e0740312500c039103410402c4031000f0b00d90181a502c0c800c800714000c143c0b501d601d00055a24091070242880442ca064420b0708a900300103000003011a41d80444250044011000c540013140303001040d07035000301000100014140030390441d42c0811585000a000d54603010030340500402500d01100503030001c10140b0a00881419000062900010180c941966104007500c00412040c21074403d0b08076412040074000000d003244460302d81a000d17600036140920740502107030440c0c0180b030b0051181010700301711150002180b600031088071403c8030032686040450f0021f818035100c910f0f0503070101c0081d400040e03000d000701c1e40600b04502c160b0f100d40d801e02d40020413242c00050061030403401c1610070816000c001c15004a07040c0c15107820701c1450b815080942c80c2c100d260200540000b2422001c05400c181c1d903000c2411703261010413002c032440c018640c42d016180b6038000c00d0707100316482004208050103080202010259801c14007401c960b5400c101c1c028a10980c0304502581290540095 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 403843228 1250 403841978 403841983
    0x905010f030e06270303060913170d050f010806060f060d0b0d06090b09160902030c070f060b0f10052205130c030b0d08091003060b0c0a23120703030f020d020c 70
    0x1141e4240200171803d6107080700016002c504040c2c18610400d45200406080c824110801c18145541d03460039560b0380659040000103000450310201c00a449200100da0300601290050003903070014080e1514468400404c40e4942c044e107a141009030341c410603a4006e4940c42c0c0e0f840301c814020040007a0001807414203082c0c4540080900c9081c0d00207840f103c2420094419002c15501c11002c01a225070321a09003000c140300310344010389506549020710b02041217903084286400d10540b15418040c007442c080c0644400c4a0241c0c00204409128803404c0b21070024581c014400004034944040f5038503008120b4a4000c8181d609100b078480484510035501401150b0790840e05071a950500e1071940c03110f8140d40140141306205003101c450f060303041403003070300b26002401c04d00c02d030142d4682ca202c03001961186141022502003c56004005001d02544014654a281c1d8000341c04060790001080c80d02d40e0000d44214107155803000c00c0b81800201c0d03c040c01c0c07401c4c110230b00141d0791008d4015030752 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 403844478 1250 403843228 403843291
    0x61208070b090d140f1b0313051c020f030102090418060b0a0b0d020d0603060e030a02071e031203090506010303030c022a040e120f121003030905010f030e06 69
    0x5032258044503041d061998424540340452541c031342102c2d2103d40c0342c290708060340300300f440300d029145081107a1804440c020000340410500c42003451880c1d95204140000001c022842051090f155510b480140c1020301000c15002002000141352007070900018007180d41c41c0240f00340c4208500d01e080c003040340c98410054210000c803080500c940c504008420103204500302551140e401043c41c010300d54041d00a100a5540882c0501009480041c5950b4075042079000d40010700c5860380005088803420302c1d0260725009403e070420400d0039038803810310041c0b0351865441010354841c103a10103c1c100b403103228040d51003a038021480c0c4442900c002c2c9003280c00030384006a039561070484011030005243c0321072000e4080e5070200e419404203085a04100551440a4030008000b0300a03c41c0340109004210000651400380c1070703515003107001c0c881c0da0321f2808000c0115060800034407066026484158040142e4500400c00c0313448141141d007807200564044100158a942c0c0744200104000c040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 403845728 1250 403844478 403844491
    0x60c08060a0e0112060e0a0b0a1b050301080a0605060a0308031905090c01020a02010e031f05070318080706090606080a11040e0a020f0d05010905030a050301080c2d04061208070b 78
    0x70b48154101080480780d0819280020800c941d10f001140c0d00d450140040e03a100d42c0c0201721010b0074605240d030b10f4060403011003074600311100c0150684c070607070091040c2c0b811395a954005000da02500c0c1d580000802010389210341c03120705000000005800b4000542c0b20f502d00100304118840f40c130f0460f40a0314000760054006400c41401e000c03e42e60700041110b00c0a80902c0e08180c10000c1d040440d0402c020601404135075020084184600006a003000c0e0046246a8040110100300c030303448481150100e9000b0711602d410001d0002080d080d40140004030700820000179010741ea880036928286440104450400d00004003400c60301d4540301c1e0901c103181c880064182044141c1c001076608919400301031080400549050600109500241681e0347c0103040300e60324a42050054080e8000b4400c1080354860b2040503e41402d01003030b25540302c440058000c40d5644480d40703481c000380d28001450340250f9550400a61072048130140b2030147c0c0185480342c3c1e24141810b000b0068070008140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 403846978 1250 403845728 403845749
    0x1030b04051509190212090c0f03070b0309100603030206060a0b0f0d020c030d020a02150c07170a0e03010606121b0512150a0e010905071d150403060c08060a 69
    0x8208a0965102e01c0d490040801c880d084581da840a001c1c2252281c81142019480d00c0814454402e03614548030a0181c10280102ca011000701d00800146845864016406030400003003000b290303100c040599040980c40043e101c44004003440c100403210309e540305400582c0620103002c82810007521850140c0070112101e45080e0f028001b4501c0383c89000d003285082ca0f8006031201c80010248241d401115000c4801c0d90b407000b10080c002e5492500083d0b089500c8030190110314090103880480e8045e035449058600156042c020301c8044e90841c0e860a0240078042c0790b101c041c0e9a00788283d5010f00750903218001d500c221076103240b0890703217291030200302001c6085620980e00d07040010703101e01d01c0c1114040c203566910f40023140c0300220280034035608920f07552408214410b0040c01c59040c0d5212900800280e0344025040b10702c02c0711034910422080b42c040d04a842418150200480c40041c220060710745540c1c0e90701c550403581085001000500c41b00144002440e009001c0d0000700750390b401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 403848228 1250 403846978 403846981
    0x812031f14120703210f030b0f010c0819030204210b010504050601110a030914010503060a0e1b030a150b0301060203030c0904060803030405060603011803091503021603090501030b0405 81
    0x107000e500c140500701062003041e40408007880030390104a074101131580182110000d1480b482c3c8900c400e1003a03040b910200da0030f031001502540c402d00c50f004445400600f501842e1200100540b420107040000346ca5010f0100703d400c007601e40500c0f0320b42e5200899034006a0b614504080b00d1104008000b58285000c50080c106001c6140c100300c076030560f0b02c1114005007646032080181d88034503440320090520f004140d00b03141450381089100d0116400351034907103c2941c401c4011107880c0700881d01aa40f050342da8101b801052440f800701e5601855110401d40d0070100030301b0040183d00101c90941d54075448031561654000c0c20201c0740c1c000c0240c0888181954140700010b9142e0100030b000781d00c60030b0007052244a40c2c3d0780750403c00040c0110030503683d80341403504040da142c80080311440e0180d820841c1402a0a4014204489441e01a590500700e213040c880708940c0603088010700001c240c0c00f44140a05210b0324111101e0ba148070340c50b0700004a15210024042d14081140148201d04d41070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 403849478 1250 403848228 403848239
    0x60507021c0e1e0303190216050d0b070f120f1e05040c060c05010b06030103050105070908030306100e0d170307090f050906062b020c07050a06020c01080406060812031f 74
    0x280f007064040383d41c0ea0410701c680600c40070a01c0c1d0f0042005900048440e0385500328665000b02d6055500c101d030f0801d00d04000d441e00e080c04514040a400100701800100001d400700c0e1048400401c0c05070302d8501012440600c818280580f24a00c10044406a4031030920080c0d04031030101c01c1940a0540c800e024600d000c3c6c07110283c1c40200d200307040c24407910862902c00c000382907100118000c2c000340110b40300c0d6102d0502d00e009040803600800490203c101c08121084d0005c140c0c0d1046000629811800502c0c05040b109510105030b86a000300c48289072100289066000e184a000022103c0342c40703181401004020031038a9114440030020007001340050f441d0345003020351080007940c0d030391742d107400031820210700c08023252401c5801d45401030003440c903c0f419001800d0fa11090003c40b203000c0c0d1a8010800200850f11800002d6880200c4031050395009140c4643d1043c001e40d00021000d9a13443d001e41010f503d91405030701810f000040150654031480a01480420b43c00106400303414031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 403850728 1250 403849478 403849489
    0x60108010902010824180f131e0602040b0a0e1c0201020604030e060d150801060906050a03060e0a06060b030a0e1b09090c0a031103010b061204060b0a03060507021c0e 73
    0x540381421809910308200850b4082085028440740b01031b0400e04610340c41003484c400031000303a52040d40700104101240c03042d103c407400c2102c40741e00611307441c2c8403c14000c03109080c040c442d1422510302c1d4080c4000110300d9021009091140010b46a070b42a000c010800c00c40ca0071120140c5285074052400240e0150741e0004501d540194542800b1100503402800030300f450080c00e032028003540c00c3c00e1a102008280d080401c046912282c000d00c919030301c0c1c08609040d6181c03070261a801a00214042002c00d03c1a04100f0040381824280e810f0502e040c4c4503001911900c0d0410044283c1c00014001c0c0d07240f0300c1c41000c00d442c15030809445011421580d186003102041c050714801e02541c400b0440c0c0c0761080c0481a585000209401c640c140e1300c0c078100c80d9000403445514401d52134207911a1a5007060000c55240340d40c0d002a500c042d03555135843d41c0081501005907a006403801c00701000251491242e10302a941c140c0051810341c02c0d074140e0113522900e80c1d40d180c0400c440102403840380c3d12003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 403851978 1250 403850728 403850731
    0x30031308011503170f0c060711070605040311040f140901020310051c0303090303060503150f100b0409090c26011a030c0405040501090203071e0e1902211501020601080109020108 78
    0x160b080700e6030384d4440c0e031031702c0e00e4900449149080c00e01a5000303010a85404c030010042d0b4031300d55001d4075001380e92044107540030300a80c880907040b415020100d1303045241950000c00c11880b000710004030003120041002c610300c8215140005a0342c0002030064108003100703901d0040104440e010b00c4241140c3c92081300030700b07000d4002d09040d1102c10000c10103029401c0b41000d00006030884401c1100c20201ca241408207a6200c00e80c40e10b40000300d204421b4a0006405883c0160081c03441c10b85406441001003c8224058882c0c0a41900102d80d5910014158450300945084003900241d41c85845003100c103003001c4010341100e070b80c008403e15103001c921316610701000c440015540d0b0f80c6007001405030105c0c9900940c1801100b4000c2060491100c600200204009544504507114035800c1d00c0000c06880c0c241412801d0084599290982d400420b02d00c2c144039609800325404102d42c1c1c0d80d00b0003e41d0742c1d0503401c034440c10748100c650f0304210142c01080004001d00c442d40326030300080c109030300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 403853228 1250 403851978 403852013
    0x160b04060323070f030e010902180705130e071b0b130f1a0f151807051c0c030c02060c070b18030d02030f1530031308011503 55
    0xb1900e420750300c0241e40b00910025910b1608202041d454500b2001304420300c58084d80001c64940444144030603414860440803607800b511110300312074480b00c0c40340c031a00d0041101041001c01c01401030035607640a2444000c0945845456083c10003c0005c1e0004182c1e20800e80c650300c1c01c64400c1d000c5111001007d03089041441d04410014442c140842a20082070700a03203d81e90450f81c184041c0c46000400e8481d81e1200041c07882520f0300d088034203402071594146039002000d003c1c034940603400f42000301c0e0841c4060404610b401c03201c0e5a030302046c4402001407511290303281e031280c002c180c160054240b003000501c0645001c0c074004514032210700411402900c42000c0307400241c42c807202e81c030381030040b41c49900459858140e90300d03031100a54011500088600e00100115101540304600e1141d0035a00500e9015100584980c10500d00610110b00c03020f5811031003040006d810500061043c52452043c581d01c1c0d5040c6049a420f58641c20031802c000c03070312810200081411404164502c130b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 403854478 1250 403853228 403853231
    0x6050a150f11030c0303010f0e06090c040603020f0930070503030d0207082203021905090601030b010e0d150b03070605120604020702042f0307022d010504050708160b040603 76
    0x1100442d082c1c0c958040c140d44054544000400070600368554450b40044996428031040c0c40d61700c003004d0014a020583d6402101c1000340010f0015500903005050404d04c5e81141c181012600c4000500c014500314081110f488400004072040800f5003001510b010001c0080034218a00f0001c40d03624851481e50650391a40400d0394010032600004942c009202928a80240f45642548207501300ea1840124451031074840d09004036102007401c0411158010100700c125582c0070015405400880c0d0214100300324140c000c0225a580c5041c88003039400b516148081c1d100940e44c03541100d41500000d84a03600c411002c00609501c84221481c1480b02030310350311951100e50124000e03008011000b0340c000d05102401c024040ca080703003900390030858800002014481c030b040d0f03042d5100c16980b440068012122030030034001445c0c444070317842e040040200700f80c1510130031407821070754103490031200c40e0080c0c80c1c2080020310400c4030420b0142c04a0030910341c07518012812041344594803642d0180b5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 403855728 1250 403854478 403854497
    0xc01050f0114090a1407050c0705010801050918010902100509010215040803180f0a0f0201180e0a020903121210150906110f0d05041505030105060307050c0a080406020106050a150f 79
    0x240e000d90051001c4108038200c00d4850f08162801401d00c2d00a848c980c21580320703900e00050303203600c12981c040c106c51001c0d200c41d6413601d801607418007009102c24090368964803a4514001a151860700e00380520756569482e403228a035034002810040ca20007005c880c6032045060202040784c2c1802c50743c01040b0701d5030b0b0b07207086203510a4044c108014001070080c1ca00402d045072003841a41e40c0401070300c0b80b003684c9250307414502000680c4402c0c494003800040180d600c1c0003500000b003d80c0100060800101110b040c15000c1e080303400d5580c0110f046409921a000610020100e1200d810f07020f040f807582e40ca5081d14245c840104440d9840c81420200a40140703041c00301070302400880c421901030410380d1032500011030090843c0e07101344501700000031900145124a841003003928140c607801001e00d4555220700000b11425048500c0b0f102e040d019543d000800034901800900080030705400100e10a80f400f801c01200300003c2e8007100f81c03444e203a03043e00000e50380140d0301d100180d10741c180b0842c0f9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 403856978 1250 403855728 403855741
    0x10203090c0d050f120d0e01020c07090b03121315021b190b030708041209120206090609120c0406120812090c040c0305091c050316030b0402040303050c01050f011409 73
    0x2d054a03c890580b036401445045031544179640000d242c80300013954240465140700040600b01d106030350841e01246c102040034400c21926410804825034028105c4990320114408504268010a4403c800d0001d10900f004a04100300c0d0032040c100441c005004410241c0c1c410303e405c00c200c10710f014440c0070b40c65001010b00481c0518000030340044031081c0c2c0c8910304800054a0060305403800d8860201c01042100c00502c40c40c404410f903001041000c0006e1200d81c20320440c4d400504031070707604c41c0052082e030b031542e182d25624414142003000100b001c01c2c01700b0203010407981c0541040030010304403414000800ca1300000c41c1c01281ca14540d107851aa910302c0c0342e03410011042e1540764018188050102c0e5154150803460040748590709499881007200140f030041d44654000402083c024000108030b0004c1d00e9440798140b00c0303403c02181c941e034403800140c2280e106030030403400b092020451940031002486203550250924090400c254141070071080b0a000c441d000c203100e07020110000c0e41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 403858228 1250 403856978 403856983
    0x40305070215040602010c0909060506070308041e1511091509040f110c0106140d031404080304060302040815060a09021606060807051201090b010611030c0a080d0608010203090c0d05 80
    0xc0302900c2c00a069112629007000901900d180c0c40100300203400a5004540c44042d446280700712500200480c0c60001240d4040c2d1b030340100100b0a840c1b0035580b800741207040500c0002d01c600d4500c01c400d940840104508803004407848a20842d158800c203101030900c503207032440e003021499000c0032419283c400240002e0040d01d640c204851210742480b181107000c08800c000b40045070790700002030001c4d64445002c0984030142c0c0c01000c5e03010420306a4030000ca8020039a2001154600c841c2c0c601d020380b00c1544604d10340c003a600c508002540041d0070802004140301d60076460400d55180c00030740c01c2c4200010003010140c0a2241400d9001400a4001218840e0441c50651202007800016a0f8405003500c603c541d200c1c2074000c500200044c544a50180b00c0c0044040c3e00581c00380199003031001c00c4a100c4030b002d030441030500c41005054001041005840c584520480b0415a180090101e08080d218190f100032456070040c0203004c10288007003101d60301c003007055034240740000c087d09090b403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 403859478 1250 403858228 403858249
    0x307050412060e1002190804050a2d0302060103030e0303031005150702040e060601031107030c030f0504090510051201021e0f040f1715010509041205041a0304120c02090403050702 79
    0x8480c4142c604004d10559070307402408500d2580c0d5070741e02c50f100b0140000d032501c800446000300281c00084c005400900c2043d111100c041040302c104140c5130703040c4810344c111043c555084d00503a10843c0100105a1300a548000d103070b4046c3e000c0c40c21030400c035080c0e4005135071500650340301d4204400b25071002031240b02510003841c0c008009105207080c0402a54403500306036010390029003450b200c111b07030b2110402110306295042d5125901c058181c0c07002c84180000001d480d00b0410104000600703a80640122401421103040782801245440c0400c1507200010280c10844c0c0d005100f20307402ca09202c1d110105042d03000301c1c2e16a440c000700e40c10b01c945125940101e03032504201800400e04060a4134182c0d0741d1030340d03030b0111501034143c581c7c41b40c00e1101c02d200e11588002100000b8000500354102444140018280141410b488030400e4030b1140d880d0b03440c49009a4080b00700400c1c40060401400c0408450800d00303090207440d0080b03201104010009000e21100103840000c6459203134890 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 403860728 1250 403859478 403859501
    0x10f18021f0e1e030106151407020d0b040b160801060c03050d0b06041707240e0103090c080f0c040e0c011407021008012c2701151703030705041206 65
    0x103040e9801500c03424501d0000b000310b40c5000c0d600e8001d003c503050060b0950000c528810b51502c07d0f004074030341102344281d40022001c0b13030001c010704030342000114080c0207180900d00c41c0307840980f01d00d40250029210b81c2d0140c850410002d40500401c200b54000703084900b500c7d01b518000c0c4e43e60316844400310103080644509500724900003400220114500c03070301d4141c5d0052000390303440e40c0d6442a5544001d01a1038449982154003049849898085c0c51184d8140d54107060100d8400981c0e2984910303c0f145502012940e04002a042c689180600806501001c219410000c0c2c0301c00c1d2280076604c0c00c0d6007a1050510000c0c900080300c5540507015034410580c0140380000381c41d820b06000381601000c2c400d0781d4004c1d4100540c40581140e040350000b81c010b02400e6503200b6529425509045e2520010f088954285003c140010300028066840c45294810007a0116481d00d036568041d210307040415400c1d50020310a00440643c0901281d0403030b00c1108181002c081f003420b100004100980c01c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 403861978 1250 403860728 403860739
    0x40b032203270531022502010c02041d01110f160206040f080d121e020d060305011a0117070f0806040e0610090b030706020703060e01090206040602010f18021f0e 71
    0x20b00101301360b002401400e4000c0050000600b42010001d4241e028002c001e22040c0c400c0c103c07070320f1004000408a10340b940149007086016605401250441c0d42403441b000006400e000020300d1301e0703024041c4e03844000301201c102d40b0306840c2c04210009400340c01c02d0300404a15a15540c0155a076200549016003500b0240180c55070b0348809841d55018207074940d1b00031541c400e000808000340d82c4200c06103042060000d5840e40014018000254010364940400d15510b490200102d4805d02c41c01760070220349107020301f0001c504e6002411000e2030b00030b180403e40841003000204ca03030000d140300b088509030600f909281ca841c4001005040507400c1d6149921590303081000f510004e030f110004403150403a0402c21800140141a11212a4084c03080540c1c402d4004100044c916800310341e5011b01c03000000b440d40c4c02e0380c4c00900c565001c0d030700000044c0e448103019449007003544103d03e016203441d07030510502c407041d5000c500c1080c3c00c015075140240c2190082e0310082d010380e030703090b0707203040300130407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 403863228 1250 403861978 403861999
    0x190e01031e1a1006361208091c0c090915020712090e07201006030f0312020301120303020a02011d03042903060d0303020d02040b0322032705 62
    0x1140c90314030000300c0300c018002c07a00381d1000880c90f02909030714144100101c1d07008100401542d8101c140d02c0c3c00342070210b8500005000040c041417442810340c2d030912030400196103800704020000c01d2035806150315861203007160002700042c0e42c0c152400460307002090100d070707154290801c0c0c100c03624140740d0180c1003400022500304114450036445014206a1510352400d620340c0003140009500700e8509000c0782c0b900740000c944a0360481c40000c4c840c001d000700d480d0280f030340304c2c20300c250741c030551040b00c10003482c240400405401000e155520070b4035030003c60a56150540e903a0240d000b130b4030050f06040d070004d2400358483c801e401170122428100c03441034920701119041980d036840b0f8800c440740c0040307182d0503c01c2219a2205010303030003074942183d0304640390141001180e6014010813402d156003040340c0e00e4800d040f400a0b01c0100006d5040589078903211100080a06100d139a100d581d96001c0c03d8440001d800c001030541c11050500f090100c40400c1d401c035000803480b03402c5140c1c003103000d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 403864478 1250 403863228 403863263
    0x80d2a060b040509010908041a0403080a050c060c0f04060e1c11192303100f3e210114030f0708070e0a060e0a0b190e01031e 55
    0x10400000480c003524200301980d19110315500306c900210b001020030204000403c12810000d1080d0484070492401070f141660700d5956410350340c4081c0aa10100c7e10214209d8600c90081c005243d100302102c0c040d40c9010f11820404059120360b00804081c4403010080035034549508180350b801c0c00220604024422203414a201c50f8900e0340c1c00c0900c640600c0c94421110740441c0c1001088440d442501160002d40512000813203000c00303115a01481014641c0041918038016158401548140018540c924001102042c56244000c84105480d18202d0001b000f0101112078140083e00026442d2139400c00781c9940002d14061040c030010310400003060002c10145e8100308001d00710200e0b001e8510002e1010303100d02482c4141c2510717404c41c40040040071043d070495036214500c400c000a20300d8680007003003000441912010700c00e554070841d145582c14541c0c02c128006908001c035003521490300c0025058540140401040c440828002d51000c406503d2607942865204c404441031040c0d15 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 403865728 1250 403864478 403864481
    0x3020a030b030d03051009060302060313020607080d05010e06150d09060b04090309050f04050c1c1404150501170307020118030206040605030a050105010302031306020304140d090305010510080d2a06 87
    0x2e481b01d08085801c00300000d0304c0d0b216032040c00102ca50242c00e01782107a540030b41040c001c200d0014103a8210350108824070004140000601064412440000e40340d410001407240315100100f07070602800e0721007034100c52010708100340c0301c025a02d00c1001c6104012442c100c40a008645455500917080403449020541c00c4602d080c107031002680d040d045146a9010031058620a07202d840a00314100004c00e00d0055000301d5440301d42c0000800300d15041c01c1021500b0302807080b601a41c0c8010012415440c44010703000da640101a003050080383c620fa00d103076160701d034410644000c0c103000801381650402d002c4850310900858004002c1c41d00c5941d070726005401a84200c4108903000c0c640000440c41e50302034401d03a8010074202005600300314083e91600020360015006440c81800e41c030270b002100c08100200c106030500da685115072140b4601c0c140c1d082d200060b00441c8600302a00090201d240002050022003100d443c11841c00c10141e20f90000440c0d42d400c0c1a8034a070400d00d10901400b095 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 403866978 1250 403865728 403865731
    0x20a1202010e010b0402070b06100c02100f030513052e0203010e1e01030809060904020903011a03011404050c10051918060309020121020c1006090501080f06010603020a030b030d0305 80
    0x405001303222207030410b0b0400040b4404c00e41d006000c5e2400002041c180c0c1006c050300c2034840f0050400040300c81450b000200d040a8809080d400200ea030126003010b503905001da19005001c0144000715040c4c2641e905448805520300c144c8030203164801290422900c2400900800c000f500443d03495031075080030f0308000c02c111078014100c10000d00c409107111890780901c0c1203e402540c02c40c28111150708008071580500c02080c2e216400780000d04159030300384514264000d80501e00c1c60886410000d15017900c41c0a51340e0500311f480002040080341e004184003603500b83c00c07206001302c07a407858003d40d958040c22503001451168040c0c0840c031581c010f21103c43c1300b50300545845241d5034a003411000d6400410000740003c406020140a10407601c200c01464441080e001d42401d0304900e2044c60442a810203006458880c41d0030031042103607201d410701504180c00a48916226080c203181d4600061146c41d0416900250f0401220311030f1703104902c01d90000f4159503484850381c00c0100503250 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 403868228 1250 403866978 403867001
    0x1329040c03050706020706020c090703020f031302090a06230d1707030201051012030e032104032117280227100311040b03010b030106020c011b06090201020a120201 72
    0x3000da010904c28000524142142c6040e80102580000c280030f000e10380c80c1c0a880c50041c103409001e581e1012024a01440c032a0311312150104044880d40100b00c80840e01030601040d40c0e1034003006009100c00c2d41e000007038021048040103815850040450a4403900000140001912500002080c1260344c003c009441c040d50091025466208565030800d1552044050444041003810002401001280122280101038913000c010b442c410703103040748003c52480440b0310b00207030510801250700070000001a800050103c2c810400101505243c20a001c0c0080f2140f20740c0095000103c04c4012081907408646110000101084500c06500103403610307450200300710381ea0741c2c0126030001c4039024408001c00c0710449004118042c0c004040c500103500000100308404613200302d05070001e44c000c10b030200c02c40343c0c1c075890040000e04140d60149040d0400850168042c007424038441003c0100e508030b80006a00b0507a4801030b850010a0b00000b04403207018405175621640640c019141c0c0301 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 403869478 1250 403868228 403868233
    0x405030111040608150108130c030b070224010e0403140f1c05060301050c1c0216080403020102210f0903010b09070201050105123d0603080910081329040c0305 70
    0x1214441c400c02c81c5c40141c007080f80014007120000e4a0109558100040d582c010080709000c0c684a880d14000301c0812142d11025a01c001600eaa010110048401107100f5a194414465040040c5003003419070151010f410884500b00c3d0035294010b4008503041980004407050f9102041d085480c10044034030070b01c0100618201c0042d9290406002c1d0610030006440b1181c507110f0f418000311002403405501036480c40e424000c0703d40140c045c90607031042c1070040803615140c0b8510f1000a207003ea03014402211020080b810344200c00904042c1c41c11096402c0c80d8548858000340403a004110842c82544d10200b0300c014096a650190700050680d4403e5519040c00c00725100c1c00c541c1c07028044401c515820300c45941417000c52704032040200c102c0b03501050a0564425202d1070302518456042900c2c4140c00140460852504698042c00c0c020282410510791420400c2808019101800035092011040b0050104c6200b03507415452201301d04101c03030040c2081e051800164645000450307a51 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 403870728 1250 403869478 403869481
    0x40b0f010909050601060f02030d060b0c06100e01030f15090308010918020108150f03070617150d0209070504090e070315141b070b2404061202060f0405030111040608 73
    0x7140d060190301d030000e8015000304407992034400100c03104003039101c0350380450200b84801203800e030711030140f103008007000c2402948034400c425026086c0f450150240740c800e0000d54080207050360a0b140181143d80202c0001c122400d10f00300740f510718494080d090140351411800d10205600014980c0c1a0307040041c0400003149070001840c800303440c42c58042e0102d4000030000c1d500d2403528444c6400030201409040c1c1c03240202000c2880c24605030041340c041361194108a18566107801907651100c07010384a13910b50b8060b040802ca400b15000000b0f4002c805c9003001900350f6000d401114000c0c40001020080c01c91380140090b25100c4500046a0740d090301c8103441f0030184240078400b0302070031801180381d840c0c58822103040442c00700142c000400209008a1010500040e86d6510481c4890b884000c1001002e02d1003c80003101640306104030301c2c014040c044d07200140345000c03203d40c1c16988a90f40d1400001c0c041c03424012a80410361560808103412140402c83c0d01400885105884a01d00c1e0b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 403871978 1250 403870728 403870739
    0x90609091704050a1404020d05090d020f07050a03030c050f06010b0901020c031612060b10031b0801030302070b0a11160e100509060f19030501060f1d010b130b03040b0f01 75
    0x1d0344914400d079540186071010600c000c0c3c49014641c0407056004000501e0709030050015400e90b40c2c100d5030f15040340c00845003c1d01c05501444085000c03001c041c0900062810000019a070102a00000d010006001c0b0035408118081216000c45c031400c10071202c4560350b401c203c0200e03520660504c0d0042c050455100f02d58100020600840507410300382007c21410303d968006882c0280b08160b545507100d40c4082025154032002c102d0064099402284000d03d15205480110032040c0b56410404c0003001000804d50108241054402c42c100c002d90721400c3e090308507440e0b12203609085803030042010502c0f801d1120704000301260313070420401c1c09683e01c0104080e0081207601c1803d0b0040d0003a000200189088000c103560103100501c80142a0400c86c00301c40b201e1103e0304125102c0c0c0d5240d005206056016100310300074100b01341c8a0304003114144110110420601c210f034416000070584110b80300d2a04440c070094503030401d041340c8a19190074400c01131803040e11111409101d61001288 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 403873228 1250 403871978 403872023
    0x405011805030a06110706061805060102030c100f11160c05090103050c010f0c08030f011701180f0807152406081603020910030b040b03030c0a15020409060909 70
    0x21503a0080c0500442d03141d40d104c0c1c00c082e011181c1185c090041c20031403074000500c244908409440d5000c522034041c0019441002100c101401081c159131044c04050701e60031001492200000c580e03072020421114051011010708220480d0a440d01d0700441d0340700c503005207019113130a40c0c1d005030405985e035503407034050019040c02070101034000d8002c0300d01c29050354091800742c40701c004146402040480d058030364080540041d20b0341c4d07890142c5800100018081098034030702001950000300080140710303404c012622200080208402e41501090040c02080c505451142340c200740c00c000094010000100100021541d080303810498026604824030a626400c0503151239031030f81c20f0f0359101d40c209242e0b421048080c1c0020940c080080e5416034030350300030036003080304a03803008100b01c91640200000e407002104401e0103a4000c0c820f102201400061880105400c1070b00d544185484140303110107842207802030441d03617040c114002111041680042c0310f079401102d100340c142e0004804442d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 403874478 1250 403873228 403873277
    0x3030f0a061217040e0705070302100b01090509130b0903030f0c0906030f060d05070b040e0a090b0105010c060e011406181b0a030204030c0b04180c170a140408040501 73
    0xc141000c01c0c40600005030000708048107280d00302e5103c5041541d9035282401c0e030300c0112144000904085500b000301034040000549601c440710303052100b5500c800008240380c1c4944201031041c484180400e03008c030041da01011213aa003202c20f45916103011605650341e0390043d610260400500f200080500d44001d09407220343d840148560b180d40c4520300302d61003526020303025a50040303112400c0f4000a604010b41d200900c540540507071194940040d84004900042654119509011410000500044006056803002d080009610300c0c1030409100500d000315082095610301a00a81002442000f681c80303020216640c8468015500b00c0b4140c0c468192040118194600f01f4151180190030140000c00454640141800d590b5101c8400c14a21684400e260700c800280070300c000480d00485c030f1030a89020074240125804520300410003203252415071101000d6202280c182e100540001c03a500720441ca00103020300341418812050f620510680f40800d481454840c0c1e030705854000b20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 403875728 1250 403874478 403874489
    0x60f0e1c0b2202150307031e050106030c03110a032c1b0607020904060e0a170405011e120203040309080109030f0807030c0801030807140d09030201020c04050103020d0f020f0a060203030f0a06 84
    0xd01344010221602816000075002c08181503c3c0d0300401144d0341c41c0381d0080f002c8480d000700031038603515001000e000c5030034599008003018100300c540b4480790000300894011a21501e03000441c0400340003108210115403a01d20028002daa04520904100040100702070306410741c1494090702e180c0c10410144034074080203421000ea040003402242566218a200100b040309903140c41265503a490004a6130300030074400d04a02182c107101039603000a80200006846080c01101d60f210040600b10800e00e4040004264000000074100351041c1e180c4002451100c000f4000c81c01c0c18603006e0300112401c100040000c1041b00040d041038424020540340700815101c5201d40c1c0d0a41d11980c00039808142d0540c0c600d03040c000320802189041015a2001c0340640d0741031030041c1184002805c18520440f0135104605040051000da075804104440031544884004140e5a43c1e02c0800c01d54071000455030341c44003000c0d0000850540201c001d510804071340401c41c0c03099071850745240231a66a40a40d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 403876978 1250 403875728 403875739
    0x11041104180504060b0d03020714120a06050709170303040b071b02040e03091206010303090501030203070f0818120405040b0303040b070b0702250e0709060f0e1c0b2202 74
    0x102009909500c80d50f0814095400481ca075803444020824003180040214010303840000b0411101104001c0d0340c019040803a04200700c03808076100c15070744c2d2840d4071000e4100d40d680d40c00b00d152180192845001400107100e4078107000d480d10f00c01c40c0c680d00101d80580b101c1c03581400040206100e0044c4980516040840c5200003a02d9000e00c0000c0c1070a810b1003000d4481045002900e5403010508c9040c440d2a6006009940c19440c004013103240940c4603e041c0360041c014403180a800c00300185000c0054036100d0190781e074404403200c0c070300403c802c004201c0c01000350245600781d50000500640328140e8081c04100c50901c00c0c103541c0c0c0b046100d01d07101920184101e0001428848210350080b1051040340c94102d080f14075403085075a040000503110402603410081c0326040070b10107502030701c20308041c0340707040c0b503c0009083c2c0c00005108104000d10095100400c3ea10004001100d8521a070303413519003545032500441e148c0d13080c0e900c00780b00180c032032044400c1c61300504004415503000d400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 403878228 1250 403876978 403877009
    0xc0103090203030f071b030c06020712051513140f250b0912010c171e041202030409020c0706020f0604030e010c11040906150f0b03060d06021611041104 67
    0x241345040c3c10008040310040c0740028040020a4421040c501039805601c1c0425003071324101d0043c0c50421603078040165240000401c102141010402c80304001035041010040e079240000025030240c0800d0041080c130812810581c100c40000385180c1548040b01140c22140d200d080615180d024941c0c0821030841e0032601b8000900f0a401501c1380c2140541041400031840400d107013500c51800c0c04100250006080b1014089501903ea0704520403070440348408170140607000f05401c006201401d401200036812280902c2001103600030b050b04c43c0119151124095101c0e1584030500c6924014814035200c07401ca540701003a410700407545921005c00e80011071005442c03c4001f900180c600c50307034088140800303444500070500424410140052001c450f0940403240d10f40f990000040d42c0808101444a0071000c01104c0c1c110000b101c8c070300480390561804002a00c04c00c0303084066921403480c40801c00185a114109048007110140702d00343e000e0890306201e01440c4203000002c0c40f26007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 403879478 1250 403878228 403878247
    0x40b132303070b180d0501050a0c080f060111100c170a1e0504051c051e1303200d03090f081207030309020a150c051203070e01051b07170c010309020303 67
    0x2002003044c5200c0e888404280540c0c94005416083c00305001da4440c0d4452040000740d100c107104107096284241018041390920311902c00072a8001040c1c6410b100d20030490500310740701003103101c01c10390207400180000002c41000500320388000c400c502d03400441001061400ca254000c0c214a8501c0d011030040e50942cae410880040e10010b04141e600d8000d00300170026800704c0c4140160641c0e850344505658078481444070000461000c042caa01d20001d12030b4115005001282030100c0c0d030440c00752800c401203045c52144800c8080080c0d5070250710302c6c480001f007640240072403040b40c40c0496009590703980d90000545070000107460300b600001c2040310b400024080d602440065001401c130815141c1c8a401c100801e81c0902e0341100880d0945140301c0c20000304110918902c40803110350b90840c24240c0b80904a0b030030740c8c5010390500c800469113401d880c80c440501e003442c030002422689007a94804c13485400580c0240700c100d1900500c80d00c0f0440d94043d002c1da40c00c641e030240c0218034044086 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 403880728 1250 403879478 403879499
    0x4051e041b0b0406051c1406060d0b041805060c120403140706060801060f060201060b0901030b03030706021621090608070306050d0c060221031902040b13230307 71
    0x44041011410409402150381480b040161014003060b846090b03079261500c41011004030412241c01d19541072141103002c00c0118100660441410b0b80c1d1a92036240c85082ca42c0031303002d040c0691360072914002c01080d80041049803c1400ca000e0000d030b0301782c0d803135145000b10709118151a1311030405800001c100000d108d11200340c0481d144540c1d2034107060b01c90355850142c40c52a070000045a440710070610001040f800311b0741c000c2c0a180020425140b03860030502041c01800305050606940b020445c1b8142c406004443c05a0f61200086694491807121001071102010f070903136104114480c4030040c4941b40b1202e5102e000c043e203440ca016840c01e841281d5202009010380201078852a002880703441d282c0c2941c080c0d5105040c0401d1442c00c0820091a01001d2418151150903100201181d05404001c81c0c0d00400c0b1003802048440030080d88401030301c07581d480031401400000724421100004038008043d03e8064800d80404c0300310a400001e040d401d0302003e070307241e0040e03035080000c034401c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 403881978 1250 403880728 403880753
    0x16050304020d020418050c030f07090209041b0302030f010f0506030412021905031c0606050301030f1a13060605010503090d030e0c090702150702060c0403031112040b0904051e04 78
    0x602103081044a603000c81d0507103170340c160031100e0b40f45503400003010090140204522440c082e4010090440d52910786651003486101d5807801c036500190300e074104d4980d03812246c201400ca201c000d0410100c448010000d61084440c0c400480d00c000011803900040c0d038a01044500c0201058150b48a5403600296039000c400c401007903220f80e55020224126012845414a0003403020b1070300c80030104141101141e0620600e0165450482d00b03111071500721080e2070540307420100740564070301245841101d418001c5d014064941d2244200004c0803024010345034500e10892040c041c0d544d45000544141c081501c01a809810000855030081d10a510907000380300d200d412920988160408103c6206007039500d0b8005820294250265050746003a054011080b403006011074a425044d00c8120b008900004081021441c02c104499004103d402e00c207039911b00c6020354540e621802ea2105074440d6410b40e02403424403001503800c0c22184404020f0700941c0801800695865a451074000b40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 403883228 1250 403881978 403881983
    0x9050a03020f011e0f0e030105010f12062307020f0a05120f040902070305090102061f03030c03050903010c0f031401030b2a03070327030c060b040207140c04060b0316050304 76
    0x104208682071540d416503030031a03d220607444175207000b00803040007014100441d0b000e42c060ba062200400c60001c4036400c07030080303a14041902d1006051440d10340042c007030030000300d0300302d85507103178038030381d00c0c801488440d018003070340e8084817a5601a030a1091700c03101c1031b0030040d1094010f1081614121142001002101040e07543c2a01d400e03200c82d005000c9030481c1c2c90940c001032000c40e070141d465070100052034001c0d4a144c050f00710301442d0041c0d0981c048150100074102300b0314440c540b00b01809501a1f6600000c0200284158550051300400000d80f485001700003a061032200e0007006032400b00719050ba41c01c0500018180c2d54218010b040380c1c4a41d4400300c40e121040305c0d0100d00c01003c0d003c2e40c05010b00f80d801040000000c00344000f141c805001d00c110150b10079051400083d005640410300036400600401c0030001040020028000d0030001342c02e01c062141101c459400200f400103028404a4040000d180c490f8101043c9010440b4071034520030201034800350103400b4102035640b091 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 403884478 1250 403883228 403883237
    0x8091b030111030112141501050d020105250204060609080309040c05090d0c1d010503030336010501091401031509084501021b120105040308010e010609050a03020f01 73
    0xa00024045050380264040804803009020103070400840c90a03031000f004c00c003c007d00d020300f5200c0d100c0c40740c01c07018402c45210303451440062046900445c203a400c0d54085404072104641c07074800d03c509000c039001c42280312f14078040010074400c0c02400480c1c10b81d42d405008500341001c050501004000341800345082c4001400385409550712207200507803013403017100c0c620501482c0c484440e1002e00d1001c240024580024014402030300d000055992180324580090301c02c01010748040000032028004070b500104201100700d0100381500710034101c40012004004000c1c9110074925800760a0100411090411703c0450821004c0d80056030341901070741c4010701d4400c00c0d03040750b10002c1081c00760605045a15a56002e132040c0804501c4607031030440c40d88000d03081c2400000352100001c00305603200c040e50104050b035a85803a203c07102221030302c40003000325040c50300700580380040920032070203405082800407880e01e10400c000c10484a0203050b403a001801c40c0d00308103000d084481101e0420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 403885728 1250 403884478 403884491
    0x807031e0e09060d050727060b030a051009050106030b0910030b01170705060a03060302030d0e01120e0a05100204030b1501050a0f051c0218010306140111030c010f0c0f08091b0301 79
    0x1a205101c20002030a00c140940c0c3d1f42d6500b108500d90310f81003c070490151518000c2c0801445200d803080b2a0b00840032500000c5965403e16410206042a0000446146000004201c058056011191106044464480325921003070341e1108886280001006540302800400c2940c030300310708400040101350182c1703800f5619a00480c41980186503d1800683c503040101b041d400c0600a0010b8041d40f80350141d1303403440310300004e0816802c00030300b10f10150f5154211040f050080c00443e10749540b202c20345041560500041c001782d002400182e44400500c0080b0f40c442a4404801280000c180c43d15414110b00c1c074400e4032560103058400c07051280400004880446442c417a50a80641800068403000e000c2c1160074041c03101d41905050511b461000e00c40c0d1091428001a0303401e091800e0052082103840302d50860007603032500d00d103a41c00c1c40068140f12560b030f0441c1b511040789549400984d01c0200003200e03a480c041d40d0f001040e0704000c201e805e501c4d07100d4403443c1c1507031800350001c0703800c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 403886978 1250 403885728 403885733
    0x6080118110d0b031c1e030209030a112409030106050105030106120c09210b010b16020f011b0c03051b0f0f01050f0f030108010e0307150f0f020301030807031e0e09060d 74
    0x80301c20f1000008480c280c1020b4650950010406c0080f61403404500300321204000c282c0c1d030040000e024007140d040c00d0318045150760792240c40d03071410f540740e00c150034017499543c1c1c190040e046032104500ca942445d0000c00c05502c15816241207505a61b02c42070401c07003008160f03004241807500304e000c1028403200880d20045100104203200e1350307031300108818001405c00c16010101a0000720320b0070030801441c8020b006407181c14880b20340445150525165003401a920803001c5c10703846080e26a85c070740a90521240b007511004490064059605400c41200c2c00c1030b50100410b50590700c038052180401950a01441c403450149060400d031b0319084890740080c050390844210704062070790001c0180801c0c1d070207001d444a664480c07c0114240a03007030341c9070050800110181d0850325580c2c40810760052850b0480c0c580340200210071075480d6141d04120300c0c568800070341a0046080304194480801719002820304808061740d0f8a6000c030303040f50400c41c0c0341c00301a0009902261003a500d070007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 403888228 1250 403886978 403887013
    0xc121409120f0d06260106080304170c030a050a030f02120418200a09080606100503070302130b041d15040b0d080c060115030606050a11010906050106080118110d0b03 73
    0x45c0c108201d14000c2a03901c0710f18200e0103220030440303000503410a001044481800020b490503113a029104942c40141902d440745007400b10344d03040d640362280000d04003d02901040000300070780a5524003001f007140102c10380e501c5a401540c0c96000b8020001000501000c0e83d106d8517280a0100218007421a120385804c009800083c42420440004000e52102d4204d02d04400801c5400007a01c040c1c80d0003400681f41400c0c004007a014480300000180f540e511a604585035888000700300703841c3d00d0310f510049046030018041c4543e000111491003108459041d1527a110300e052190780a101c01018083c400070300104504290031001c44140031001400a0014080c008002402080c0561406940c846061010b0b41c0721400d15241100501c1100c0c0d100c1d04840c0d41180da03003480d4801c80010203800d0f00420310010044d085a2a060001c100140d02184060407511450700c5095100700354100e038400c4230090042070000040030030002a030844136401c25035070300c0c1c401026510482e0661520700e2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 403889478 1250 403888228 403888241
    0x20c0f0601062c150306031906021c020304121b060905010207120c0506040f0809060d0f0e03040503100506060f030a0504200d020d05030d0c121409120f0d 68
    0x80116200d402000c050b24420803c40601e8500c080c481210388001e4800720b41580503600c1402e034140c0d40040001c14584042100e86420b0f60f2a070601030707004101e4100207000750004141200301c29100030001ca5503803100c0c000c3c1c03401590803200c0748088118920b0256a0843c00814038400c500740701041c080850700f01d20070002c00f40d000d00300150f99140e152806440c054280340d844804c0c0305c205011800030038400962180c1c0207512a1185809455030b08180041c0d014080f00d181e8803100000710488a010f0940040807500705002043c004000b840c510203840b80900c6c050907416070322a504666101c40a500180c2e04954040c100c50318007214641161000c1e4011607107004015110800d00c020031050304150600700444405029203800054001a0310003455a0041c2c890040607103a00c090181c1401201c49109500300e04114260582002906e090440b20b208141c1d0f520b4007405440203450804d40a20410581018001d55001060400100d4000145209007104144988628a070007442542c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 403890728 1250 403889478 403889489
    0xf030b030304090204080c060a0c061802040c02030904050108030408030d15050a030503040303020706030b0a060c1403160201020601082409010b270901090c181b11070e10030303020c0f0601 83
    0x540e417542081120f906d410410700b08980200e40c100718000c0602da00115448805a00100208030704407510800d40315015145400fa41c070918108408801b01d40000c01030200f440c09a900f40042c0c0c0c6ea40001a4503401903103e80d020075003040200c00c000340c40b241d124500800408495002c1e058841000c6401400359800848247d4400582031061640400802e4000c000e11b16080c8901012900401c125800c9071240c10148001d0180c07980410100040d0380c00520394040c2160b444400070302c010140e0642c0ca40007a030150003403000100341d144010440f82440c00ca2600b5520750704030420f09880b03101900924404141d540e805000e20991388801c1d485101c105a85900030304a40d94002c6da40c1e1303a40c0301138543d009030313031400100c58002440c90301c80300c00310382c9829003140c4a10040351011001e00307050302c0200386194000c88031501441e0801250210300d101d10007103c9031036031601c0320000c2d200707825201c040349591400030800029202c0d40080c05c4002601081d2100c6420100503d46400d600f0b8118 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 403891978 1250 403890728 403890731
    0x210703080a0804170304080d0209032e060b070f1b080d0e040f0b150d1107080c0115060e131d0607110703080f07110312090405071d010f030b03030409 66
    0x3800148001002200c0880b84e400f41c2481ca0b6007015075841c140303807059500c81100c841e0041a54076095074207225170240e1000003a05200605101c41c1030369551610301c02c40005903450b00401141c001c0701c0c0c80565002d60b0340b041d000050f40711240c4843c80c4000c481000074180d4010000b000c520b090f0244400341d051101d54440410b1402c1e00340403c001d65105141d0030500c43d1030904410340560316584a40c2400c0340c1040655914901c2c03206040140c00444014100382600062000c00c10080d500103001078005440204010700307141000c1c0c12031044070700c18940002c421100404161900050b40b207950001281c00040203d8020142c54044404100b140101c4c3c01441c1041521900030304080350b00119200a40030660940e88c520003140554400d03e51001000b180078810000d0101018286610042c215030500026954200c5030b540410f02190040782444003250360180603058401c4102c5c820341d20340044c41402001117400e121811000d808258450706403030b0b0140c40c1440104042c16440d05c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 403893228 1250 403891978 403891981
    0x5210307050309090f06220f060605040e0606031009050a18110306181902060403050613030e0904030c0204051e10060915020c011101090803070c02190302210703080a08 74
    0x4c00c212854001d01c0c005a003040c075403c01a40fa520b4030030b107520f8050070000d400040c3c0719407501800108661045d601c007192400c40c01041c0580c01c400980304680c1104080f101c651b4510301803040501054420161200810360140a50440c54001541c024283c10001a10840035070704081e5103140f11400f51100f10b0f0380c2d00010740906080c480c055028442500120450101c0280d0b50360380c1a4040304010440c5c0a00f07454421540d50a04960045400500311100b40c20021100d03440484082d1046001c03940014400b807850400d50000d91240c1c1e05501c0f00707040c08405409010190100074801c0c28903499440303032444940003819103e4001d681d48180140140d0404c0b05c06040c4030078542052010202100b4807913403040e130000703034620604000c1c42c1450034020002a11409840622402404c82030044100580716a1008211940a000300c4000307002c69a0020348001030030b610301019411501c1c0f484400d08036641446a444407200c40c0c1b00300c8410300c0d502c0c1c6640c007403608150f1030000050303903010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 403894478 1250 403893228 403893247
    0x2070b0103020f040c020714060c120c071a030105270408031801050417070203070b18101701060813020a0306050a0608060c0702010804110d1101080c090a052103070503 74
    0x254903ca2600c03007030f90f0400a004007460041c1d901c0c039040c80380008520041d10b444555460741800d513121141038200f11282c10001c01d1400500e5000403007040140d02c902140011480e014207507000c0c40d0b40c1300c21511807860f400c01c4144140d110003400e6516070b03003205402d44420b11540e184450b10480c06481640d4690a214004d80128001c9070380100301681031805001c04544402a00c10b85081d1443c101681d481d61880440e0914020b940450030462000c2001d01410502000d0405d404208071200501110000c0c000d6810100c5400d10300e0340c1c080114014004140145866034110a200020040080483c0d000503054811504102c074119100c80501c5511f0304140100d001030310841004e0711452034200d9140c130460068400c0641048400e4001c40d00340b000c07a51075522805000361603480c0b401000e08002540284100405002504000009035000e2041c015110120001000203024515150402100c000700001a10700140000c1c5a421001070800007003a40500c00e40185840c0d00002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 403895728 1250 403894478 403894489
    0x315050106020712111e19140a080d0f030609020c070f0b09090708190608060403080a1a040b0a080d12060902070b0708090a0215070b06040902031203071202070b010302 74
    0x1358000803a0310303061100c04d400502d095154401100040d605c40b0009100c3d0018400d450310701c42003558000300951100362400761410020401d076806420b04000b807010003003e1003084040303881208480c0e08070005400e035039803044030403500c800c15503e804201d4503110b0b0840000c81c0c4c01040d02c414950b00c220405c1104409092109000308040c046007810500d20300013050401e5401082c0008100e541000a90281840c980c00000d01594481c1013100320b8460310700940d03501099400364040742481700020100b000324011201e540b0805400d101070388807a5010310020703244403c1ca0603481056a4800305080e40c1c10010191055810f603980c01120314080309680c1119950b801c02031045004001801c085256440e07074a411207020301d0208030030794881039068140360382d4410080d07003d80d0780a21030484c000c8080240155501407490b03c00c403910f4910410080360032505000b505a0040c03014201640c46180107541c0c0700d8290b061a1020001c00d43d10002281d00c20141150180f101c080188250300f0039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 403896978 1250 403895728 403895743
    0x201270f0504061721041503020a02160807120203030c03030c0a17010509060f0f10030209030c1207030803071e03270f15060e0906011a04120b060604031505010602 72
    0x204c03606007134824112280c2c540300c1ca00505d040301c2ca220035050144a400c25542103c0041004030f8a0608040c07400310010301070750090801100600c11000c001070351550644020341209c08000c0200754440c541916426891a00c2c001607905000900184412400500055100c1d80d0740c6540b003071303a03a901e50708040c0a00035111000d5107182504001880380340c403150015a00a202221010806003021000684010b41d403c183c075040703040d04e070100000030380540142c440d860049041d00c511001003414890154011600c44502d64800e990030008201280300564104189140c904400728007541804941b01210f0384a800003541c40398518085500d0030030602c20207003225143c000440d842e8403410980200440f001d001c5028a410040c1d4000c1a6030101008040c890701072941e910b450031444d80c90b09424070920b000752111101601d01e02000c80103c40c16500e240c440a01840304a071200e4980f1a00180a1a0000c00030807001c801303e14400c52800907005281000304817503060400080c2000003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 403898228 1250 403896978 403896989
    0x30d02040f06082809080c2d120405040902030f12030a0c0f050a1107080a0b150105120403030f06180207050c121203100b13080601050102030a08040201270f050406 72
    0x85000d10005804c04180315070203040d5810502003400061410030288038441d01200c0344061154450581b40c0c2c26a20074050300e03101d90f5020a4680c00c2d81c0c0051541c84030044802444032075030800060240d8602580040c140c41c0c0080c1c04c40c0e01000d4000440e501e880e00da00040c41c21100048100100c13101140a02801c4103102d182c560403480110344080d003079000d07542841042c000c80360000e00c54094100b103030000400005044482075442410b001008020644900305420245041010254014022680050112180c89141d541c2d681c80c11070060440480d2170001030340b81d5a00180005501c2551a6020315036500185e8a0340799151051405546490050040400c0000340110304408140301d9125045081e07010399958034800d48408281090300401a550303004519025802d50b41046401501c070100b04071409640c84d280103a03928043c160480c80003802c0d401c0028015403281503402212075018000c1d0030740c0520b108841c4000700480e0001486208404001c00c41d601c1c00707003d00f100610 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 403899478 1250 403898228 403898251
    0x9011505090f06012309031902010e010c05031306170604150b0a020c030703051f02090a0302120a0b0f07030c0c0803010e060111120405310e030d02040f0608 69
    0x1440d00011400444000b000007864540c00400a1001c0c0d0060900e00284050300211001e42d041c01c12a000e41504115030702c5000303104d00f0001d81c20000c03e03140c400300100c3d0140c4482c0c0c041c0c551180112200341040e10100c0c2e143c0018020440400005001000035103d0707a1100c020f4041e81910560b10050020801da210701d040c903483c4c0401c400e42006a20607a503000b507916680b03030003000c07040e8584140b010006030544504680007007840004641000d1038080555460081956035803507000fa40500003045902c031000d09005c00c0103203010002d1b103415030904800d1369249902a10361a00a04044984e07500740b980c40010804071603454402c5074002c81045c10700f207441c040c15860300120380c0014020440c1134019603011030390030382c041d0180304001309891040302c10f02c1c008032950b411950410b10445010300f0751090b50700c0154150a034040141929004019034601010748808060400d9a417608014001000f44250441c1d540c00284068218922403491492401e08000c000c0c1b01e00403c29030154 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 403900728 1250 403899478 403899521
    0xd030513020a09020c070f0b09030f07061b060f02030a09020a0f0806060603180a06061e0501051e0f07050f06070c12111603050d08160c08210705030901 67
    0x580d10b40d02d02c4029582e150384010f8a50414030708452904126410901000ca0704400000c0c01502c4000140190041942601d00640e00950610b0f030b01c203601c1c0035140c040396400d01c249005640c242c4e180400c0501444021a00c20491a80c503000c80e07006803441c1301d5842d29124000194284520031000402428800844042c0b421865a8480c17001506113849401c000011404480540f10350000b0000b510098443d41c41541c580300000302160711880c0003072015207010050307201c0c1e500404c0c8221441a160700b46040c4503102d042000416030104000c0d030715401c2c4100d4042c201c040d030107011503512901c014030342000781c2d80301185060301c02000c401c204020402c3c1003002980305402c04070407a4003400c0400e25086074041d8607050961082840050a0a43c4000000c0c0f22002656104401c240d4442c1040d03070311001c114040c1e580d080612540811007181d031140018100c0c1008102c030140b180086010510000e6203909001419603100000a00120900070a09001e2040c0c4420590040310b44020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 403901978 1250 403900728 403900733
    0xe01090f0c02120405091003140303041101020d08060d0c080609010b0f040204212103050f0906060603280207030302042d0501030c0215071806090803032a07050d030513 74
    0x904ca5130203001e000d040e035000403403042100009900c1c0590791001d0b401e941d0441c006111660f81d001200c05484101e1f540c1800041c95002040e40441040030b59103004040d5101c805010301c442800302c080302d413000390500008410fa014049940552075040000c10a0408442000400b500d4482d034944240d10411003001041c031100407040101c540840501c41c000d41c6811315200c16206d581c4003c01c10780d440b0341d00c0b01d40168903903c8588141d0f60001340c007100351114159140c2d6040300321005034200008001040341080c20020040c030145508851410081082d0700c0001a0703084100c0c00c07130200342c0100f014001171140d00c5014902ea000079182c00707070025801c03812210f1000da500c40d050601d035550484a18462080c031860702007103048bc0b0790083c5800d041c1740c024100300841800d51074500d40c07844045170f6603100c0c41a420440340700000445c29619181601e40c40381b02070501485000c0e040c60510000b41d0340ea000503000b59400b80c0050103000200c07440140035a08010064142d8480c0c1e4640c4400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 403903228 1250 403901978 403902013
    0xb250210021b1219181205070902040303050301031e030e06131a120711070605031b031305100903080f090f070602070602190203190c0807031424130305040e01090f0c02 74
    0x84564025404c94400018181f150408025411402820780000380c04400e1680010080d4100c034401ca000b130001240b640302124041c446610f00030002600c08002005514200010300f281982c40349480c0c0b4640c2d542d10b908000d0496403401c1840034100813460402c1400c00b00811a403200e030504240d44480003944900d13803660b00901403481480004000b103481c0c050900707400e0000603012502d0750380da0304050a09404071190720300704880d41e01c40c121464000c400c860007210400c1e40e150b00c4d0150152035040700400042d078010000c81280c400e0307250078410800c1c1003241c00010b00583d00074140035400c040000782803071030341920019541c3c694000c680041c0c800146040344001d5012034004005582c1c58520000102030303100400f80c0c4180e40e4080180000d00080316207103000b1108655120b0360080008114881c3c1251207101c010306c510018000d840300d215410b2050b840380c86c3c001d1405844045100160000382c11802146548044200491030325100e1001e002c90b080c00105205284120150b5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 403904478 1250 403903228 403903277
    0x100b09010e0412031506120b060a090e09010902060f04030c0803030408072003030d0f150302030d1d0306040b0718030c12020a080a0b250210021b1219 66
    0x1400381e050b00f01203800e028400c0e4007004019080c4030140103226070f160001000d601001e1072070320007240703440d405102614116044481c8000c054071075aa1941c50248045a500c01c0202820290354a9042403001652400000c24000d000c2e9064251190300b54105040c03010006e4002c011281c0c01082400007081d0350341c4c2500c1d92946c0c40b03010f00300c2c3d6016124604544007a02070000c0d415101c00300394492030704d120341c00c8550760580d04a420040d12510001016031f200c1f4510020390141c00081c5807003103081c41800c4039101142205000d140354464080840c0c075000003200d0956200309001c09000d44164400a007142c0b4032012285c2020b10b90550b200d88402120740d126840d480d4031403030300e0030086450f50328081e0010074520007600e110341c21608001c4560581222040d04240c801080000c0c0c1184220030038034010b0751640140b07500741141c80800c000754400d080c0c0800d250401c0f080c088500604104114a848220284c103840340d80c100345820a0555202d20f84c0c0c14802c1e8010310311002c4401100c0d04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 403905728 1250 403904478 403904483
    0xf0b070302040b1213021f0e010509150703050f040308090a0602011a041505030106080d091502060103200301020a090e18060f0a060e101401171b04090c02100b09010e04 74
    0x41d0b00ea60700950384a800d8045d000b9044402600c450000088400114001c4580c50700c4109945d00b03040c1c0115124822500265440b20b80b0b01426541c450901020b448802e2103401d00b2403400441c501c0c0304002c1c2e0410351003140c4501c0001100707251800c10300001402840385000074000c2c01520b44200c0400503103201d0041c0034940d00d0300b018041d8110004944000e02c8003500070031817544c492410948a0841c41c0c15840407400045001500c00c1451800d10300300e03c0541d018000e184d09650719580307001107060380203400345030001c96009156000e1006104208498440403141c501e030186030078107480010070380b160440b200302550300003400104815520004080241e07103641c2d900001400280050b800c50380040c8049001c00c420070400340c0e0000e05840e01048543c0014140600442d147c0b0400c001d8201182d044001040348659025001410006110115400c0988480c0003404807011422080c00680c803e01e10041e83c1052441500030500d81950700e500e00350f040041e540031614024000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 403906978 1250 403905728 403905757
    0xb070615060e0d080d0c02010e1603030f08062409040506060c0a0b09030705010603140c0301270302100e0a0204050609060105040e130b010f05090a0501050a06230301030f0b070302040b 81
    0x1c010420121401720741d641011200304100001c11b2000081c000c0581c4813600c00030780b1450442c498000103071080303001203d92650740d08403e40300c2090300701c54009002d48401d40004002009488060032142110049070b1020b1300030f911100880100000d8500190074a030041c403042200089611000c91001d1206400424054542d209e20740c21900e0361044510151540d46480030220030029011112010b200082c0e08407030021202d141007600700c80140601750b951400150051080759014a48240c1c4103000b40191680c0310703c031039201c83c141c0320f08445844094210082c90030440c0b0f814402c1c41d800010903146102a131a02c040003900510030b502a120b01e41603000d00041a04400c10400102c0d1a809a208041965502d0700c0c1c00301a00140a840d21450100e00040c007410586c3c85024125100280038081091601c2c00c15901c0f0034880484c4100c000030440c04240c5d09942e81c004600851050070078509a42c018180b858071007101524180400d4010002004a400704100782c80034034130000311 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 403908228 1250 403906978 403906999
    0x33804120c02030703020603040606150e06040e0601170702060105151602040b0a031509030e24210c030709050108161b050f06040302211603050f040b070615060e 71
    0xc0c50138880f0f078002540304900204000c200240c6401079821100402ca008510320b4145605490049001d040d00d500000240010880c825006100d180c022030103040010507410302c1c08064148401c211045d5015a00c0000108441e0038001d90558040c040c00344400d0520421703c0d01e00c0ca0301c0b9a0820040d204548a0081c0f2040d66200f0507410004d40d8400000785001c103158100d00050f20300342e001507020800880000c0751034200cd40115400c040d8049404005410010740381020340c000165a03c00780141607100c0d603804018103a6030740101d440c074103010b84a160910300200041420b070001410441e5060520100700d0140d11a4148200c0078148008000c8002d81d01071500780c039243c0050028482e0304bc12802c40d420104905008034000e50a0301c1311350050681190b4001c0c2100d00d03480d450541008800c895942c000381c4480340a1181c0740c55864200014040d8025800680015080501c0012b5446c1080001d2203413203d00d401191007400d4491034544064000ca00340c400e507a0050081c0007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 403909478 1250 403908228 403908233
    0x605040b0c07051206100501211109040911030f01090b01061b200405090303130303050a09020d081c0506090103140a1209090e0f06040318033804120c 66
    0x800342c00940300c05481034007984880b2903899038a082c203950a000041c083c42021415500c0745030400300d005003080c0074141d0641004a0b03140108540001031503201c50612158520359a079003e180c41650003000e2020851424004060918100108615090385080c1c0040f00003980e083e05181141c0450410746450318107499030304540c03a85c0340c00060980700d4600d62031204103401d0a00030000340e03003981c042086644900006036a444107561620950480040c000c0000b4800d4100c180e010b114030002041d0703c2043c2d40402e02c03200040104848040b008203d201440007030031003451540c3d400800c140082d0a10070081040c000047c0405410b103030f082e404200003080708005a030819a402030302c1d040010b0760400000c0001400e4056003d0f8141403400d111100b1600003094001080d00d0400b8115a031100d82d030070f035220700d94062030746079104003484000046104900d0030030030407001031240c14240c54503107504900c0303001d0140003400940c0040d0034040030a44402e0a41c04071a62403d1411300d460150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 403910728 1250 403909478 403909483
    0x507080609090a06110301060806031f0914100507120614132c0c0303120f06120106030f02010807020a03120509070b040b0c0d050f0d05180a06140106090605040b0c 72
    0x12400741c540c5041c40b036114480700c1c0080040d4126000749e560048941c550384d007099280d00d104129810540e03442005800d485050354000280b03d485180e901058001d041010381c244542801902021aa5401005000d1360007241d040541d1920190403c50681801080301a00b4010b000d0a4010228071480003d24461540300c1d04010560906143d900c07400190550180c0e51000340310074217806801180001030500000b07407002c00311007002d01845a5148a65509002c2c0004c00712903111200007001c0e00417140a1040d00041e5000c5c100005021016000160611401030192411540310f2043c00f0040b0783e01641d20201085079200204654a1f48440c1d41c0c07502101d604006045c0c80e0000e000155007140f0700c01082440840b0064034032080b14240281c6550166002e8008080701c01c0240303101140566100715400b00d40351200c1d41038060420130b140e140070244c12080320529900d01c0c00000c50582d188550780141120301d800120705080c140300604034040c1c1d00c20450711541c085015018000103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 403911978 1250 403910728 403910743
    0x61305151b0d05060111030c060f0603071802122d090c03070602060a060b03090a081e210f1513060803070c06030c05030403090302121e011509050708060909 69
    0x1d201191901d9020403180c00038201918160b010819491340452080c0d00402902d04072100700002e40f4241d6258078078400301040007400e29615010704400402e0b03050311103500f40980001502d0060300e882209850707880d20346024050741820704c00256408141c15454000d0001007810f40109030013900c4544a103841c1c40101d0300603590500032781038045070a80c0d0026000d88a0246c000051240b2a9940350310440ca110a486100c2d081d0052442500071414201c000e10803803200d42c1d400c000141108601d00c0381c0707400030100104609001c81107260426014081c298200e6041c4100e810700d824025a0440c0300590720748500d0003521034085034a04840654000c00040c4040c1d410b50f651000d01d443c202841090741e00a15010034603042c807902d0030b0b5209000741e070f1040754180c503010791090458080010104200b4008061841041d41607146420440b4448170760013000000410f8024030075188103031000382c6030004c2c003e59150400b0440c0d00b5a20070003842e0031190a5504d5141515444806814203e9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 403913228 1250 403911978 403912021
    0x1b02010507061401060e0312040806060120101d060c03240d2103091505091e03090a050126060a1a030604050708040320010603060e030c06130515 64
    0x1011800082c0a0b074102407440e0700d460702201925100004808e1540d034900450258007800d42c8100001486540038884059100448200c402c0c0325884800600b40f4101403500a20b07a503e88031203040f0040c17018000801c6280300c000015015502d0035042e207112601000b004841c24151180703049490741c043e05000c0807103205c081c241c0d401c0302c8900e080022800d6a0803000040032141c0c9140b9480c1d0310700c203101c0c240300c65500541043c0c82c60031302401c140140c030028001440078000e803050340d21041068080ca200e0008803501031074444010404004490b0070303d510181c18410014000c10901c0142401c410108404806404035a1191004540305000300c1d041000d4031041484030341e120b003000001a512441d402c0300d09000c1c0b0758800904484200c42560700a001c124120456107500780b81c00300d20070006d000180002200c1da0f8903250201647d5401100c5c1d0750540001404c05840d50b8240112640110245c4000c581c8070390a40d18182d8440c0c49440301c4280e20410000300f685203644500b41c240001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 403914478 1250 403913228 403913261
    0x11062a070501020301030b1e0103060213051207060f050f04030818090a05040203010c03090807030c11061606060f030314030c0d0e0d0e2209050705210c011b0201050706 74
    0x1041803401d90b000f50300a00084c0d8403512004002015024400312071040790981200100c1140d280d556124080c2d00303c1a0141c46451407040089850b84800701c10002da07161f22401042703c1460710002410a0f6406840c0004120303040000d42c8000014a04550842e544440c04035550304030b00c140711022000001c05180d00c00502c0090040e10002034000d5805140200d0080150400500c4207070201c0f405d881004080400038002c010201e805900241d2400740035100801e40006554009900b03684101c2203913941481816211040c04002d00c41c8402403c0c154012030500b40c25a18043c0681c480741c900217400304400000120101441000d5030544001d42400b4000d035035045c0001d40d06d80c01c44802d0721000600e4003c50004900e0109540d005201701080d00b00300312150300d001d49000d00f9035108161194400c000b400689600e941841c22400c1d00030011144001d44000b003603e00b00222000704504012024400c0000941c11024a215051b42401e050f03039117421500d046405481e007166002d03800c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 403915728 1250 403914478 403914487
    0x7030c140f07083007080414010b03010c03020705010b150418060503030a09090b180c0a0203040b2a061902090409060f0b030d0c1a1801090f0b060111062a 68
    0x1c40001480e80f000900b03803114880c0f40700c118040071200344d000c8500381c0c0003078610302c00f040c042070002d103507410120402000070629155510100b820341d50034055810020703900244102c02e21030b00388100303048890100c81780c1d0030540d00d207120b50300300e40154090888054040c1c0d01e0b121943d005540290000e00c0094252501d800341e11402a00c0c1f03840314030031340c0c43e41410101030303400c149000f40501c1004402c43e8480c000344e03200c00040d040d40e90090380c1c00c002548010800461005140700c09401e00c56038101c0d100c10314469140c0398640c004191032164230a94420700138440d03110480c0fa81e010a8503c03583c0c0060300d0308043c80c00039006c1c003805000501801e1030040e01081c00c0d202500a010310400035000ca032009a040c1c0400c65101b06072510141c440300c1400e0b1085c004005007008107412007081100030724959240b0301080e003190072105048500b050f81365000e100700004840072a0f03200d2001d00b0588001b58001d00500e0703d9210041c0300c00c400400c0285031050300d025017001001115030300c0341165102d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 403916978 1250 403915728 403915747
    0x130605090708220b010f090e0703060c0c0b18010612050c06160b071106060307030305160305040e01170c09041208041b030b01170a0201050703050d0f0504050d0807030c140f0708 78
    0x2001021b000c2c4600030500064040b40380301c0603001c0c44414240a10042000341e156407100e80c010145c4484420421041c0748088020540c0e441a040c000d8003603184000d519800d5000c000d003104c060780d100f0010309800728880c00104a02060303c04c20400291003a40d03030b0306141d400c0340310203050152000703002039000414000c000f54000e07910030b40040500c0c12a0819142c003401c043ea00c2d2124400100010002c1040c02c400700e2400500d8504a40700f41002414292101250005007400742c100f2081d0341a41c1212418074a0104840380c0329003010f881046071428643c880390f050704280c0c01e222090014140c0800c0412108812002c0103070204844844801d0b00c130b192036507a841c000e100707050744924240420062080089891620254140c5076940350020655040d625a0449024020f520f9580e02c075010508030035010b03036489103100d24050000040d005002510140019244004140c64030054442150b0081c110310700030707680c46c000c0b06e440303001e600f501310540d11a044005000c11000700d414241e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 403918228 1250 403916978 403916993
    0x906030209041103190501170a02060706021207020d03110a120b03070915170f1e0304030507031202011a061b010207020d12020f01020703080601120f150513060509070822 75
    0x902c5c9168220900140e661341c804080c2d4034403d80c00140303058004940450041ca0203000400040b44103040150800d00c080e03141c5011308404507140c60158005081c4405216414840d480c048114926070f1420540d013010001c040d4890750390402a4155118509216503074100451002409000d81c1844041205400c011103217030030b441548907000302004149900c1901180c5082545080402006055005480e003080c60f869014400068001044084046902030091802550003000c1c2c0c000040380d41c0341c000b0708640000c401d403c40c49005e0034820b04159990421100012260465030b910f454a036200c0c28028496418000c0d403001c0300d45527000c1041900d480110405070b00c0e8003580e601da03400650f15402d07132282001c000d00046843c0d000546560180e10b0500a50241440000c2c81062130446c40c02150b400a90000a41004180410151038924080141c400848506001061805020a01c280300c003400c460180300e42c40001030445811082c0000303140c541800e0f01034030310f001da003084017 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 403919478 1250 403918228 403918261
    0x130b0301090606140612070516050607080411010509010f03050a1d160506210c07050d09180e0601120f050d0c0203060604020a0c140f070b18100906030209041103 71
    0x104c4440054001600d00c0e161083d02c00aa949066101c4e4650398403a08481e685c0c8507820044141c6003990100000c02c2c0108041481541240c46800043c180f0707040c0584000d06107030300581040000c219650135a6070010300025489400d080c041010740b03821070b5880c007a105881011560756000290034180d00d8000404074040340c00800c240c03400d1a290424001d50703118142000440c00d5a2207440440710741680c04103548071222403406400c0010316901caa0908020220140c005091028144420909000c1003113680c0c1159004104081c942211162075680510a01c0c400754030840c528814000c0270419055900e82c0310081e1070b000030707100300c000e0408a5072038005e80c000d224040c0001c0050a241c803c544400b0000d4231078910080c0c40e0350b0340366951002c4031070110542c0980b04400f0080e40c0100a9a4064545c41040310b40b9000100e558500508403d090740c0d12179001c900d0711002154000ca40e50341075540f2441d0250b90341c10103e000c90040c240101c03580d03030070290000c100001041c81040c2903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 403920728 1250 403919478 403919489
    0x22320102090a0806251707030207110f030d0513120302060f0a050f130302010f2c12120a180b0402180c030115180605070b01060809060402130b0301090606 68
    0x40040b036440700341540c0c0d02c01c82182e8000300c0c1500135105441c1d40d0121118807403a6038003440c194807043e6400c0e20036010070710b0035101803000c207070040f501c00108811044d036426038110666846403551a01d200003a5613207047c0031000103000e40012480400102d0078141005041c400080064400180c41e000f5038500d003c07039892a1040c440c00201e0104080f43c0500b034000c0002078505945500c695071488100c0105040072002e56507138566080070075450b0300070b0621035107909142c440010240e00c540441030087c2c1c4010b11058001c81d1912440f00c413500306440326241d64640301407039690340b08410300082003240400c10b03500c0f111803c48402c01a054040340e100358401c0da00705d120a0031811002014030019240500390390001c0c40103101c42d18180c444070a0444540c6043c43c0700e2003080c9206100700003c3d400910015000050420a001e01800400e004140c00d00d401d81c0c0526120301c0c0a625044058402441032849000e200d500d4030301ca030045042290000d0081001a0311450240c0080c503a61060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 403921978 1250 403920728 403920739
    0x1306020607020c0117071b060515031c0807120e161401080a02030703060b0c0703050f0a0308070c0f05010c030603050c040c17090102070b0705090103052232010209 72
    0x54416440811044144030f0107841d24000c065408281101803600100000c0820400c407135100c645034210882d1385201405010000781d141455522101000004000c640c02580300b4581c0c1d0100e600c403c0c40400030340c84a454039600e241c45044c01210f41034880c1e0343c1352400358206060348962560100300113440c40c800288214040c0d60382c00d038800c00441e18045290109100b6070016400049a40065500c22454a0b00142481d1100103080081e040500951461384c0002003e00403c03200f08601d00101c11080020503069006581c000c0c55801d00914000801c501c20303103400108403201810b00d5501c0d9001e0001e00103c03e18490080c02403900d84030036036092103034144881040c2413505c1850040c20301a9118002800500c641141761000505032030702940d070030031111002ca0010710000340100403d0399240d40ea010008001000d440c0f001d0444d1803912a174003000c1d00b032601c00c1039080482c2c981c49a204403030407032000440102c410041e039294007012400b40120b00c0317002040d03001313108180c4100c0b203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 403923228 1250 403921978 403921981
    0x5040501120201050a12240e0a02030123060f0d1a01031a090405030903060708100b0f03220c170f1504032a14060f060102030a05070c050613060206 65
    0x810003000070640707020f0302080042100b920b40714400d03491010920011754000c100310600c0c040b100c40c08105060404034000e00280180503540344002c041d608010034803010350565050880c01e16521945000140d5828201402d42c0000e8071407000383c2d00008050a4096152814074504030003810300d0000300c581d401e003101001d2501d50b02901ca0015094000120081c00f21030301e0080c099a2600a0010360302c905c414085020144d80800055100d00e00750756544400d03040c10458401f59608980240c01c0c0b80c2e8080c800c40306801280c00c2500d900c0401c03d204220440c404100300e800082036020f015102900e070ba2404203806864000700b00c035000500c4110313540b81900b40d01e0151912012549c80540ca9102c1d0f001c50f012a120710285520b40072131040c078160114640c0318032540000b91400403241c6250701c40d007030380b6010401d214080d030141203100741d100c040c5041e9000135241d105541d850003d00101140348824040c5440e0b9032005004003a04d2aa6650f15210344050480d1003407152100501c02c810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 403924478 1250 403923228 403923239
    0x105011b0312240906080d0f0c0308060d0212010b1005040f03030503090313062102072a0302060304061d0f03030115030b091005030706020d08010b13030506040c05040501 75
    0x102501400e8041d42c0301c20a1040c48801d102c090240e0300411414120052060b070514142070300741e20000c03d8030250000c1c103545018609030074200300d00c07003031814880301c503110950a9811010000b0480e5051800300c480d42d8034400010842c030203014002e90001c0040ca14030049030300540c007040000b0000c6914140350320801030300700d0351841540910842c41000d444100000f901074009507402040300c1c01524204298946540f501c1080744e4444000580000e2007401d5002200281c820000d12014082d031600200d911202e1706641441901c003041c0c00441a0803642504251100003c1c2d507000302002c0d40e90405041800181449100084d860001510f41400c110400103802c00080d944c2c80155095a00c1d00c1e080b040b00801584000b42459140c4005031050741e204607629204203118400d0400c010700308820b00d440e10003160010015940011810f1034003d030080e58280c1101d180f14030031641c62a103d110281488800d80c401415481600248410800380c26600c100b540c2c416035040083d0707a610b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 403925728 1250 403924478 403924517
    0x203073e01081513020706140f10050a061d06040503030c03180307030506070806041d0d1d010504030212030904060e01031b0303080f07020f0f0706080f060f090a0f02040e010501 78
    0x7240c0440c3d01a180020482042d040b03038014000040c00f1f003200180d4205080216450200101c032085c80d885940c231304100c10072100c42e40f20405410251400b01607075080800103048103c03480310b5121288c4800c80f00403926070340c01040b07801510024050b251940c40d0740021550f260429103140c036049485980342580d60400043e52801c0f02c1d00310f0024000d40c2c80d940002e031104107010f070106400c261140540c411a45103e480440000240c90040005040000d0f0050284070391444100b40c2414140010b0300c0d80e070703101c000c2c3c809681d012100f021404003c82c14042c034500c50900f0158109051034070000b60600d602d4403e604a0340078074613407105070302c58400845440d034041c003005000c111540003181289014a0640d80e025005004035004079844c4600b85140040d40305008082e42c0c80040140021a408000130342c0000aa80558a05051650024042c003084e040345c1400b075105240011021710441c0c0008100040498bc21583e90351a40d0440c1c011039400d0058034089401c0c401c03240c0d40c26104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 403926978 1250 403925728 403925761
    0x609090b0f06070f021504150905220e12090a0801060609031707020301110c011a031e03120a0207020a0803070b0103170408010f06080f0d0203073e0108 67
    0xe0840101d010007004000040d0001c4100b5209060307600c003e82d0041e12480107202c40d801d844500c071912580340107200304c507041e00e040d400e40030009c4c0c0c41410052601c03590010b0000420806200c2821400300d0ba6540040207001d11411041c414107000e103007004105401800c00304000d5031694072a40d2581c0049003640c00034420840094600a02000400c0068028421101001141c00e00d40455038000900751602c080d412001c049000031110001c0c0800d01c01c1000c251101010ba0300240d996100182c1c6a1a0400404041c03401c41b40c546000c0380801c0c000c03500c0c0340c01c071101d01308602d0410030300810094100310804c030f000342c0141c0300225402c400001601d500e10341c0078074030180710303800c40c0d84021903400c0c0c0d8003003c2a019400c2c040460003a40c28000c1c0c0c100c00407959400501c040ca00801c0c03901e880d0141044a030300b03801c040301c40c100380c035030202c2180e21540e042004907003407600c1c3c41605003040d500f07405605000c0c0307100e0116102400020981c00c284150981ea207003810346498120042c5501c9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 403928228 1250 403926978 403927001
    0x103021503040b1302130515090a15030b060409050703050d20030306040b120a0305070b151806010e130e01110f0909060301060b030c0c060c12060f150a020304060909 73
    0x12180d000609040c026421403c21340d1010300300602000c0742065200594005507420b00705a55091189081c50610030145540310b090701c4420310240170394802e003280d07140c481c1c00701070700d0700101d6070014445e078545801c5010466071000496406603a41c2c18025141c400590a94000030320221051a81504210600203102030341e20207140f5649401d000c100003400f04816054020016111401c10044280080c040302802501d070182d0314000d03032606907407005c1c00a10480d00106c40380e1072000281c842460449102c0c0022050312079944601c3e0058492018500d00039a100440380214603051034175402000f80d0b103000c0300090180c075500382c802e0029805100c40306000940c00303100880052800184e4070780c01c8039000c1d000040c0d40792282210301c180e9104850ac0810300f60000340c2420300300c03402c0092030707072003003210100300d04060255030452007428000d03000030320980f085580c030100740c1d8030190801203801581103401d44c2c4102425010b5100e0f040341c45070b94042220b0740e50000780e21105004140709140c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 403929478 1250 403928228 403928243
    0x103060f060503100807150e09100308210a0c0e010804082a01060b04030b07020d080c0f090d0b07030b0603040f170d0612020f1f050c0307020a0e010302150304 70
    0x341009402c0341c540e00000e042c1444a00400f8000907240c00c107100e035002909010000e0030144034801009807142032a090700c18081e8030007204000c0d05400d1000c0c0744003500e5101302c45907652007401c4010064171003000764000100c05000140b0002041c258000110070b103c0b5240c40381c241e1001d100544a00a003210302814800040280c202d480780e404010004400825020341e404802e04004a4211815504082000c05d40050b060080c072800f4250241d02c10000d2000b402d20484d00c9500402104d8043c00801040130081b0780d50074458241030640c0c0d14143c018000c2c41e014050b904008841d1141901c040b004a45040030030200c03410700c102240d1180d5000120180d036000e180c2d40301c2e846000003002a0f00481d40034000c002d080701307403806236400030039501d080f60f04048041e004108050700000030302071041c01c0d003074260110146c0144a1000c1540c40b8240140c60b201c0c000040c0b82144141040294090b400150104805541c495007906070f0307000380e03402c1c9c1d402d20700c640c3c10103036512040d140a80040d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 403930728 1250 403929478 403929509
    0x617011403210d11030108150727050301022a0c0306160315090501030303060905040f15060b1b0d0503060a090b0a0306020d0c0221041211100507030806010306 70
    0x80660221090218200c60b4400346010302030740302e0703008542071104070300c441c4d12000004000e800410084081c0504502d0701c200d8035800e01600140010000c000c003468610041020300392110003020f07420005100140095640d52610340f5948440c001d4100e18072040e148030041c1c0c04203c0c00000f0b5480d001c40000c0c00130001500d845588482951a06212004040e281c5ca50240c40c14500000240240018080429613505510b4090140d600c160400e28016241c01c04000219091800c4e120340c02e5080400d03c9004a4800c2040f03010b4442c5070803103108131400094031900c0c0003010140b02c00c4000c00c074090710005407005100705d40c05e120503181281e01c40f02040043c040c10200e0750110004c450010f1643c41c070a80d80703640780d80c04d0741c0100206a18003640c80c20300c191007035010b111942c84004507400d41c03aa030952490320168a806540600210143c0a204c168100540c218681440b500e00070184001200e01041c0244240d1104038201c000910117004644694040d0148000b500c10140208240 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 403931978 1250 403930728 403930753
    0x120504080c091012031d0301110334020a03090f0605190314071d0a08060a0b0301061d0402190806010e04030512010312180e06100c0c0617011403 64
    0x2c802000d400040320b0341c000500003440c1482e00c042c0c0c4c10924803c1e204c85003c004046001c014110303030020280e00903410000585c032480e12210440317a00c6000c0d0000512403040807603680c81e440c141007003000a02019540d46101c2e45800052a0ba80c8030300c030f941c0341a0b80584545840070000074034424007020560030301c410104040c04c20340d05071840303003240f40c0051034004805000c10b124005403038120201c0d10041221690521310720500064400542d18006454a041d448956440c40148a20038195488800c0780543e6821b40040d001021807007003441c0110706c10300360640f240c241038034124810a10303154032450603c68425110111261000a80201da1800c0308150355400c00800c11810043c04001140d401d291300305566029600030100d907030060300b000e80e0241c03e240d0301c01c400e03683d580707500841000642c0710b815006a1214040e207090300006140b0105662490090200401e0400d00342d001240036648800d4000080b240d01c00c100c0b58507607940001c1c83c0a80c02503929160076070006690f41c000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 403933228 1250 403931978 403931989
    0x30d090b0306010c1703010b040312020f0a060f0b03100c0816050a0f1b0f030801080c0d1704180b0a051f0806011e021b03240702100e0109120504080c 66
    0x1403482c05002e049408176a80a6604880d90090300002655080414280203105020003903458071420f60000306124003183d0050b942d01c00c11004014051a00c0e40e121401d00740f05500460800c003406003c03102c107640d40e1035580b005010b030101d01c08002021080010b0380c520b01d03080074800ca00b002e41c80d202c1c900f00300c83d20110f49824690300c1900a011640103681145d174061240d81c030b0420b0280301c90200241452034024a080c50691180c051503000b020b00c0d03080b503502d0b01d035501c1580344c2c0b2900700780d24606001d00c07a65143c040c80d4820040d1500c0848a0b9486090540110100f00000c03078050780d0301c0b500d0384100a4007043c02d01c0032001c8640280d070314030140d40c095070003103800120504203e42164180286849101e10403001880142c004080c90320b1051460295420b07000350071006049a00c00d401d80a14400c01c0e034903004c3c54403450302008100301c41d00034442d4005030800d03100244045211445100e02034107a5000c100d480c0c2c3c00480c0d0610040384690207990079140c0c000c02511907503070799104001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 403934478 1250 403933228 403933247
    0x2010801061d061b071a2a010513060b0612070f030b120307050115140112090803010906050108130c0b0c070f080123040b0601030903020312090c030d090b030601 71
    0x2806080c0000c1d141441e03541d18003c0c1c0003600f6001c0c0c120798501c003c00700e02424181c09030b110500c0a0b41d2840103460014154041d22140d078005903a807501041c8046170f40041c1600118860030700d520304801e00c40c840c010ad00c1c000e91450b015000512813000f025051040b144504140300c4c500c04210400303e03c41ca1b106640e0150411030741d00d00841c0d00c51030000040c03d40440358402805036800042c1c141d0800c8000e0144248900100d80108069441d000e01c8181c00100d860f581030412150000c50b8840340307107035840000c2c0e0315004180c594a0750b0315813050000921542c040c181c0840c0010700003800c50240040842203095101341c480b40d10500d803440022494101c3c3c00700d00c1c80ba0141030300100c0c4161340a5240c1d0000d0032000000305603500b80f00c1680d68005240c0242c1c03d1184060001c100100f840c21200541080c020b190000d00500b0381e050032411030107481021001000450705000040500040c41c10140001700c05940c1c50b200d4050080d19851610310030000f4a070001d00014165600458002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 403935728 1250 403934478 403934507
    0x6070602070f120807030e06010f0509090a0b010803040302150c070e060d0209041506120b010509060604080327010201060509040f0804150320070b0a0915060905090d0c0201080106 79
    0x14000c040d400d43e203084031041d02c1c20b1581c000031116801c0150f9680d1602814a4007400800a40501c3d4180188c05992030f81a0141c0c90041448034007180b01e00c203081080e0302da255004140f0b0815942c4955001e0b4807a4401c1c40282d2068645050a0803020702640407503900c0c412000041907541e01d880c0700d000858000804055001c8404001c0c4d802503281c072141c82e44528801c2804510560304807d990085030b80033b81120202206408546002884108203581500d900700c0d40030525545070400251180b1035500095114040845d146100007a060000c50035041181c04201000074818012402c80e0b81134890320380d0102c24500070070081a108055a0441401140c0341488c09490311600e9519103560201c200000b941c8409500c41074550b504180414603c0780302ca00d1609400361a40202141d000d080c0b500c03c965600c003084208040107900c0d80412010384001d000555641c2c0c2d50b0b500400044450607241c1c0505020301d1000341c403802c03d90002560507142c1e001c4030790a0200407110f611a48102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 403936978 1250 403935728 403935743
    0xc03140a0506061c050609010806060603041709060c010b18061c02030c1207060e1e0405130209011404060b13030f0501020c0a153b0a0c030303140f060607060207 71
    0x1c4c1040561541c2c00d24550204242d001c43d0a0400b45c040c0070502e02c05a0002e101904101c051000c13035a00e203030480b90415000060030556121408a00031548151410f6603407140300091629a50081900f00300200d82049072400701419000c0e0f0044401c040844406910000340046244c41c1440c005040d1010b0340040c0449980910802c003242001d81c0d24403042910b076010007002c10109522102c00c01000304141d03042c1d680e00310603c881c02d0002a20121162059440d400003608200c40b1444804030107800078110071f440d537510f10040144070050304c2128095404c180e000700c0d2420b405000c0b60031303616001035a141218034544a44d80d000c85a04012a41075408000106034110100280d080f000d01400f160b00d21114484a030a04490300d0080c103682d841410525821040854209808203140c1c4020b1400c11701c11504030300f4103040107490001c0004141c40e01c08001d161f0b00d5449510203414421146a483d00d465505c1000582d0071038909520480401c0f075240015516000790200340d11a016 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 403938228 1250 403936978 403936987
    0x2190602040506030411090117070302100e0d0308060a06020a0203070510051c1b2f070905010b030714040326070543030f1704060c05010c03140a050606 67
    0x2035890b13070054a09440c1c900602d8024007446c503141c02c07002e0041c01e80386d20f030000142d000010f40703403259083d01c40a886074540181c0010154051060142c03d100b000301200c8125a072494098200c00341541c120f13010701794114010407900c0c000039454401c160020001c1029600e04420404024000030400003004820711094050381d40201801504041c41d8102203001e0544904041150000400210411080b046184140c512807986d110500d803840d586608002003180c2824039010709503001c080310500d0500000303818500407000e140510819600e8002c010b801d00c02c13148080c0030302d01011f05405020f444944a22038040a85079100e200340c52004d092a1480d21040d042541048100c40800c050028035110303000101900342903d1440321803458001010884000d100a031400020710850348000c0316828000841c5040c00d01350550f503400b039a607070f440798401040c0360b840d61403c0b01c4039800c0a410849003802409401c0c5082c0045400b0104c5607200720003c00070344400f5042e20f0300400c0410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 403939478 1250 403938228 403938239
    0x2d0e0901020912071406040b160215070c03050d1106070813120f080a051308030c0417030d050a1806020912071e05040b0d0308040311030a080a0b0d030219060204 71
    0x100e080549803c400701500b8054604503491480e50203550b0020710840c03003000184044030790038094515902c68075481205440c100d10104000340f1090540d81c1052002051180c100010400c495054038400e4003903416400f841c1d18260b902014941c000365140e040200003a0754107126295681c2d200085448445030b004460315003440c1c0208c102000c50010705e00795541418540c0010340c481d00b0a4440c4800c00032468040480b1100130b050f04001040400700002050394824a901a10302402c482286030801043c0340441c242d0365403141049a0350642081c00054036a000e80c400c02e136000040c8103000c00c14001d25a034038002980000003d691059104880384c40c0d15008002c43d001403d041420001e4485548120021191191340401d1080e810010a400b194030341641d91440c00b640b6003014180c90b03d4a1405650280200710800c0d09848081a00f0b04503503800f040b02c070b0080c0d081070b50030004410188103100500700c0402c40030f005640110309104804e96254031994242e0b000d4031006040c16100c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 403940728 1250 403939478 403939489
    0x30206131a0a06170c0603060d030e130b01080a05010819080d05070201020405010e06040b0a08061c060b04050108010902030a02010f030b03030315190f1401090b0309072d0e09010209 80
    0x19202d24107007942c0c4880a022151000300c0d000d0000c40d0180003483c468121100081103844000d018030301525071941c1000415009816503150b0441c020900d11403220b0340d003001d90060012004103400240d20001003143c024403032141e0b40c103850b0710304040c100c0603103084602101400d020400715910785040220b101c030401e1500c20381c0c1c003680070382c1d0000d46d80b1403911000520240c2e0b402c3c00544075010400082100c3c110340c070200c40101d00b5504000340d50303a9a10380016220401c82c0d080d00c0e43c4940f650704240c108219640000340f07503041110308100a90321848007600300c400501009400d0f621001d0000007543c05000503410b1030788903141c0803440503030001c0071034110703001654903581d44013003480fa001c80c61406c1d4042814030b07446421600d0010b0314029a03a520780001c0c1c400d00d040c9040d00101e189243e407041c0000400b405180d410561369050510081c0da13140c8440c8a1012024506e402c202c1c0120a8a4015541e0f421251540311006d4109240703410060006005101b40390b500300b080901c030f900e40c3e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 403941978 1250 403940728 403940731
    0x30a141b0109020307090c02030409091412281d1224070305070c060209040209090403110c0f15180907050a080a0b1c1a0c04030c050607030206131a 65
    0xc900100368011148141403412100e600001c1800d03040103090034003140e0000580c0c0840f05000e201003018001d604000c807410104070395103100c9008101c1ea00e803048411038010400c0030b520050082d510f450141324400c000c0070727404044001440600e254914200c1c1003ea04085003001130002d0f0404698015903442c001441a0201003100300884810483e03250070705142c0c0c0000c81d070400344014a8500401000b1800041c4002c10b0766074003140c1d41d030040d21070707906407081d048014007488a1400c207414084d0601004001c8050300b03208074034055030355051061404070403000180a0300a42d01c0d440400300b001e40c008030080d190b50928410700f0901540c1c1c3c0d4113001e0052251340c983c02d0743c650080314000c21000d002080d411120b8100303081000e150701c0e0b07043c82c0322070381c02c0a2000c58104e107103615150b6000301c000c04031054040c29060510a04061040061044a214098070320801d90703242c05008060003012405005600481c0c0050107040c10341d4007900c0c055200c0c1c800c005506040d800140100c500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 403943228 1250 403941978 403942027
    0x105130b0d0911060901080621070608010302120d1209060b030106090b090907080705120f0a03120f06030c0b030903070b0f180307051b060426061305030a14 69
    0xc407184400184890f031020301d080f21405481d094548062030f40003800141002d40481d020b900b846072010303004280da6075600c8001000a0684440c141d0311140101043d0081c04181c0c80340f064400c00804000d0b002035001103403486900d510407480c0892708120020003a0020a071491600da00028074265800c2c880d9001a106038080002e040031900140141a90000c12050b030503441803106000e02d40c40000c0a000300e4604842100c5041c1c1d0b039000030307070901c0501c9140400c41d101d503820300300805410080b03684804506450410104425100080a41c1c0d024480a00180e9411000307001e1000b8507001564060320100480e840e0014954400c0e446090840388907a035440030b8414041d103000d031304004040800310400114204200782d10380740d8403124212064032206c000e500d12001341c0d40743c41c82034034014000c04421051104c41ca403c40000003003800d4000307415000d14000956482074100e075604072503030040001d5040c051041010748088040d15006245c0c0507051001810740d12805035804500d11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 403944478 1250 403943228 403943231
    0x1050a021305030a050a17210405160b091017070e04060501050f3103060e010b120703030804020102011e0f0c020f0a110604031b14040b0f0105130b0d 66
    0x650142690051412036048180300c2e03000f200689010850018582059035081080e19220841c10310580425220700801e42000c102e030404a200b16412200000740308a0052b026030750510707010386002c0959802400345800703815040c42541010705046818031100781d0301d42084100c803a00d0b603042c007a0a0030219802000500f1894145140d0708180c010900140028284242001c0e0005560030300341c0030b085c852342c0401022507080c40017100c0c0710340404c00d51419014011401c0e40c0728101280504510741c1d95004541c03d1481008943c104083c07542c4c1105180c2d009001d56505558045503511340190042e41103649a05012038000c0c8078403410541100501000107000c0c4103940100e096402a80e5103105541009620541c1c030000890781c0400c0507804004002402e101100194460243c1c0e0009060035500100384c0038207505920079a02a2000f500a8480c094421300c00c1200380c0b40c01d0410799400816000e02e0110b00e50245000d003080f144c0c484901101e0640302c2e602c812181e04080d99102501c0e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 403945728 1250 403944478 403944487
    0x50405030a03180305013303030f030525120513110d1a0106030b03101415210a0b09060402030307060b040b1509010e0406082d15010e01171b010203090301050a02 71
    0x2401c07e140304070aa400441c0a5091519545014202113035040e1144241911000000c0c4024a5080c2c5c0740704100c130f08071443c00320610b048002450400c02c003280300343e17840c901004201c0c00c00490704109d08140d804000c240c4003056030424401006402e941c2141c035013940f200d1f1414a041c0b91710ba50b501034095540c0c0042c6070440101054030701210000d41e9180c15140c001c2c0c0c0002c407407201503116840114828081410341c03100d03000c1002c903100840301041040380008c03090815000411450040d602500085031107450b6103c21603150242560000e505500411407540002c0064103d480f00031401400013034582d0002c00402da0503494514400b80c0f540000510035890f42c4c001c0c082403c000d02c01d40d01000745600704406140c0e243c2c2403805814140744100c1910704000e001c81510700704c14085400b42d40740000c20312540021401e0071700440543e1566603001140103d4680210b0000000b00380040c54840c0c650486460b40025018080c1e0460100b080604541d032424002c1500801c60700c000140c0d00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 403946978 1250 403945728 403945781
    0x609030810090209032a0613050f0109120f021507060e10060b070602181203090103060b030705090d0212011e0c14033c040302010c050405030a0318030501 68
    0xc0d07070101d42050766028414014550241c500168a5010b0701e030314901c8410702c6100381c06140c110700d41e4000c07007a40800001400d070085060382071210201c0c0d80c242d484404c0a01c8200065950904600492842c10030011041d400306881d00b0100340928005000c1c490250101683c0411991003d001992030940b16404110140300400c450707402522900002c0001500308038528001e4070500794081c0c038081c1c01040d0300321502801040343c0340c85440103002c1c801108200286903120f0b0010301e40c0602003032078002c002405104042c02c0b2880317041580e43e4103203400d0340c01c1d02b0460001c0d0b20312016600000c0391100c60801401c24816144422894550380c40c204500900c0c95055403801c0040344100507034100001c110115010980f500001c5100340d182c0d650380101e2200c0c101d4542d080400c1222160241004010405101c0301c0d40554000d41c02800b05440b412002d99280c851031141540690290320000042482650082d4105d5400802c2042e619030383c0e142c5a003528007014402c1401440140301014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 403948228 1250 403946978 403947001
    0x1c06060f0b0318012003040611031e010602060402060403080c0a060e0106080c0a0312080c0d0207031706011d040c0302161202100608030d1d0a152007020607050a06090308 75
    0x2ea46400081c0402121440802d82c5103017405040380d540400030000c034082114581042c9240b5042500031600d038a0251044018581038512040c004851b000000c07400070701c0419218400c03030700500201d03e00340c5191b43d20800c0380d04c54407809586008101d015000207569000c2d51020103a640c0c0080341c0310b402c01124905110406034103134032849403510200001401403203800202d000c3d0341410070059442d800c02480f188143c00d034520300309100140300403c01d1b4000081c0d102da00e200c000c00160594885006440700c48030305031904002c002a640a01d960318158204065000300d91a0140c101402c80c800c03040002c0c0b95040407203c580c203040007101300d80e0341080601d5031004499014402c2503d0544501d440388103503000c42c9281d64480c0c4004422545205007180315208100031282e00001c0c0c3d0400d003003482c6180324418011410544011251f0707a4415400080c41158800b0900d0420250f0030498540e01c1014121102c3c001d004070100400c01c0791107402152030294a442040d0302e4268070010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 403949478 1250 403948228 403948261
    0x40606030b0d0b130804120c0503160302040e030d060f08010c2606010e06030405100c0e031218061204051501030f12030e0d05040f12021c06060f0b03 66
    0x202003515080c0c0e40106603a590900321052504502c156105444001042d40810b007100c0001c1c1c580540054001175820480002d1032090f0702501e00d003240203481d04201621803800c00f13032810300758880d98070900c0075103003640c04081d0402c003420483c1e1070b00050f1921032007543d540c1e82c42a0826601e0b11000c203c0290207002d440e0402c485032900c1c944441d00c0042156801d50b40404804d42001d0a40010710564000c002e0039008120080c807940e2285010f103061950b85450782002d130030a50a02450080045c012510702c014803c00070701514808200c82c1d03424043d60032621032100300c0c0020350b0001030710303456a80003080c9102c080300e86001140b400d8100035244c50664040c292016071484010000702d04582d00708152598850208410284c1060085001d0001503810780000e00030b025040c050542c00100500407100000c02d803078041d42d900c000fa00e17481d61003c031019400c0f2014000d00c10301d0b040c5906500c9107030b80c4500300010b046610368041c02828a80e42d0892102c4032400414807400501080416 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 403950728 1250 403949478 403949489
    0x2f0a1104110306090a0b060f0d090c0509010503030d02090a090c020604060b0612011502010f021303030e03030f0319110a03021c050408042718021009080d0c02030102070f08090406 79
    0x242c0c40c40c108000420000c0301d00400e9414039950b202100819980d40c0021a07540c070852031450b940310f1420080d000300814003500107c440400d0b603030000546041064155040303800040180d410140c050f1600400380d48015070b0365901c54000700001c110001c107442280c140c800e40780d0050405107030500e4203600700d54400e0b000740d11403d024030148840032586070300c1c02c0c15103004502003828560341290581c058081c08200c1d074411030011030344801c00350410720b180301100e0182d40d841e00e1415002051603200d120b0a81d00c0d000944003007000a0241040c2c548280b40c100240d10f00282200354006010701c0c9030059001c6400107500040c8050359040d540100401d0480e10343e00400090806981c3c03a0214410340c0304200d203007882042c1664414400e204810f8400101c820b090040207481d00c00000300944240d0200d200301d11030300454007100d106800c65402d41c0c446000801003400001415240c0584601c0b040364190740070440700c80012410a083c1e20201d00c500941c40e2148403e4082106450507038010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 403951978 1250 403950728 403950761
    0x3091203020f190c1503090b0117010f0e060610140c0114090d09060e0409061e0e03030708060108040c081501090f09110418050a080a1805012f0a1104 66
    0x144070100b5060300c1404c007100c0d90b1115510030352641d50416400303042c038408054840d220480000840003040c808040c60858514001c10038440351150b80411914094003c0c1c8465200130001805800e243c00800e4920f40e49042000441c404400742090035840300d0780295040e511078400e1030007600040d00302c9030043c081202800b4004142c40c0e00074200a250301c01c003c1000082c1861440c103440f9584507164844d08414240315410030400600c1d410300460314454101458076845020321039010003034a000d440d260b514007d66488810044a0040024000b964500aa50000201c0c1e0404104800004056000d051035640c9884600c2040307458500c0c0d01e00c003881c142410200007030007550b180d0002c4242203e0000f280442c0110480c6c4103107200f44010014410402c01d4814031510038050004204141c1c0c5080142d00d4014205c94841d4152103424041009a01c1d040704d890150540306881208581c140d0101544421150b407400300a00301c19150843c446000001e5810300d400350850040c0311324103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 403953228 1250 403951978 403952023
    0x5030606030f1f06020f0c0a0e0711120a0215310503090a080303040b13080706020318010606260f16020129030d170c0703091203020f 59
    0x812018400101001d81110058000607003404186036110940f007070507016040707078548458010750360704030040c00c095045c03147c00070903d002c0c64603142340400ea9101c15045007413916070200503640c0303c00421000300d0314001c01e03000c05c2c403200342d0a001e441c2d80f0030f46a0041c40307454050b1348201050034014051900c0580310b020703c030103140071150070402c40301c192600d403c985803000d0400a0450040490455103d0080e6500244203100000554006e5014500f080255114402080c841c1219003100512441081c403017200460240e0b07028580c8500c00c2081500ca0010303024469086998980050001c02c0c007814000864204901b80e58086c0c00702c00300c52020900340190141701256000f01b00104141500001408851007174020042040f00504c038a41007003080700c460103510100d020958001d1043c0c120705220548580b00180c0c0410560042101e191240010000c46500069003a01403201e814400221081c0d520000314403280268042d28102c81c2c6a0241404c3c9000003184107919008001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 403954478 1250 403953228 403953241
    0x51b0c2107212001081b040f0303091701150909080c0a0305030a0f05060f0d020a090c03060312021f020306030c271b120403030b03010c03090c08070b04051005042408070503 76
    0x40200d6040b40d00e1a10800700000010006c40080c8651f80000b40885400103001041541010101d41601c05580c0600b00060009021508031160004403901a004d0100100407489081c2e009100c8540985501e40c5094515458140340039440201100013800000800904114a09c104050444110340520090900000080400c142501079602c0703440d1003040d01c4c4c11542c510940300010001d00b0404d00c5012004240a8001c00c0907200030355040d0942c0940b040c14500c0403800c0f409030b4586035006004480e0ba400d0741002908010b1600b501031040313108407141c0359076200c54103840c0303040200c3d80d401b00c1420040084600b100504031881d201101449a6102001c4206868108190b01c00d620200e036124241100600303d044a02905035203410500750b0250303403582042c0c91080c041d002c07060b181c0755122a07003903455400307200e00c120540c4203000c180010300d0300d09059800e0003a146131060901d03445201903ca466038104101e00d4640108075862000d54022080981c045410b00b007807400c501c0c21a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 403955728 1250 403954478 403954487
    0x708030105090604180506100e07020303071d0301063803150a030b040f021e0109030201050c10060b0c010b060306010c12020708030a051b0c2107212001 67
    0x60140c2481042d4a0300003038225115644000000f410180412a00116509000744c444c0000e0b219400700b000c48090100e10724941201d49801009640d00440ca15520680c0c201c8540544011400b1880d281c18010507550380c090107414094001c0c58a031503501c544400c04045000780881c0681c0c4c026041200822803d81d10100780e90340240c41e44082000b1b482000b0004021250340d400007810500c0c00021b00050215500122203074520a40324218580d1300e140d24401c45110703050b105400600070071414001544070741c014096400e03541e01224204081f200307200080c2c0700180c0101c40d02d540041140400c10009006101084000f5031b007082c43c50170004002042c2011280c40a003000f09120000001c840c401c01007440200300005c1900d84a40c10202c0060541d0310018200084142c0303000c012050072070201c0c0e182e00055004200d005a00c1011800e0241a4081211524a0b0187d0000080d4518110200c0142e101c1d001c01001c4503450280790024078200c4100798a401010400e07103a0071540d030031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 403956834 1106 403955728 403955731
    0xc02040f0506010807080405061308040b1815040f0308030606070c090b2103030403080c040e090709110726160c0509010605071a070e040e10050705070803 68
    0x20841c08513441b1500780c0e8041c126800c0702d008110200072034401414203600c00c40701d45081555411a40200b600852200d19071682e5142c4a5202441c0c2400030200746c125000449007405e050005034002c1403014040180198030020100c1c045aa860381520304030307a8417030700d80040b850329003001c1c40142603480c10190240a07168480074880c0c2c0c0356a401403200c20a2070041d41150746035101156a00300c003401000d601242000081295040d03035404600c100b1642e8020b00e010392616034400115140c100b6422a00c2000b80006000100b2034800c010402031540c100e41c0600349c0d0303903600f03814030312070b00c40c030307204182034074444601002018100ca4045a200300c4050509a99841090b500d40c440c0450081460f4491810a02e410f0440d4038101d401c00254686002d441c25004041821941410441405a800071840e17203540030072030150311f900203114a0440c0c2008101ea455034010b000 = true := by decide +kernel

theorem cover : BRFrame.Cov 403776978 403956834 := by
  have h0 := BRFrame.cov_init 403776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 403776978 ≤ n) (h2 : n < 403956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
