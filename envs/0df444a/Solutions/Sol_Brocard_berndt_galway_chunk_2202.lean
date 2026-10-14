-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2202
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:58:37.532133+00:00
-- url     : https://prove2.me/submissions/ea0e90af-ff49-4825-8207-16a56b9b2240

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 395863309 ≤ n < 396043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 395864559 1250 395863309 395863319
    0x60901080415061e050a0f171009050a0c0512070e090a1e03020606092503020d180302061b03060f01090510050307030b101205270a17040503071e 64
    0x4400c08019001d841c4402c6000d94038035035070744000000358000c80d200c6e88041c6000c02000400d407024404460b5450400308102d59021b0b986420500d4412200c584581404c1c8541c04001d40815080c5419108010001c00c1c10380f1002444502056880c9100d4aa480b01c06d0030300400394070b840140d43c4460750504442c038a5509540345601d442d041c43c80016444641c0300b11a08041e01404503540c007410545600403d4030301b20305580180006d12038801100c071129182111800e100780c04a4081c0d035182e003010700940032002d101e00e518043c914001c0d00140103001c0400d2400b01116440c0340d20400079245581503413208801c11071802400801e1701d050203001200082d5a40310004a40745105113130b01d4541c2c49182c40b62000d4140d07031a009a491054141c40304060f8495003244603640d20030b41081d0300284a9031110410b200b0040c0f0110113081760600c039a2602031480c0b00103000c0603480d20800c5610000300302103180302094003443c01195403507040604103025450355040e10b03040c800c0b03144540c020400d64507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 395865809 1250 395864559 395864561
    0xf0204140922031806080601120b01050f03010803180301020c1e0715050c160506030a0518010e07051801030b0105010c031e0306060e031518070518040b07030506060901080415 77
    0x301d407040f004505903411350f00343c00749a0081e1000a0109081a802c07510308440001d04d00d101c1c44080c003404c2a80d9545821190744540280c3d141010031200c0d0656035615501959569040040c1d8003a0240b05850340604500703041c000c0d0b45050980000400162100025480100b401c05402c1180b80c0b1480074006170040003020b003648181c02c503448007a56090350f045054141211700030103c49d200c00c40346003041203449480c01c0340e07444481d0600c0061a42c42e11445082c01d42e0722008004000c0d0709006a640040c40c01241510488600310303440781a622614030003004070002403201400e1111110010042c9500a00006003803911900e42a04d00e4400c0340707021a045030311030708141c00196555209101190b04018028100c4208030000c0000f202c268621103a021401411f03c03a00c1c3c040310003940d50400301000404050800148140043c0d000102c58510342c9008803400e8407001d00304004207603c0b40c041c2c030909020b01000740080c2e181401450054031030540c00b0b841221451142d40c110742d280b00721 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 395867059 1250 395865809 395865871
    0x20906040626010915021213030c140313060504060e0901031707031205012c04050c040b03010f02070501020a0306170a0b13052b0318021302070f0c0305010f02041409 73
    0x4080016147c0940251075a003441c3d0043c4210600c814201c43c04c40825044051000c42c0e07503114080c01350b0a07800c00c005600b140100b0f4074a0607800c00e14240426282e42140140c02522816903404a410059a041248482081c07201400a0b42881142d0b8800c02c4204010000305000b0b0a02d55020030308400d09004954099108007050072194004ca144454081004106040b54150025480c1460b440b0700761583d0f0421a154031031a9104405582c81d10203401c50920741d450024215225180c60038214007070f500150705000001e1408901080c051101e02660b540108403100402144603560f03159251349074050b0031a0440d860051200300091000c000042ca000c103141e200c80500307040d55148200350840303a004403040c582403080c501610184140e45841480d012209140350010007040b10000f48503070500a40307410150b90080f4244031020744001d044905c60700080000d01000d0404000b00d02403402015402c00070031005802a241020b0b4254001c504803c0904942e03040704540058044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 395868309 1250 395867059 395867093
    0x3060b041206290108071806080108010b030708190812040609030e09060f0f04090501020a0521010528090e0d170c0a0c0309150c0209060406260109 65
    0x204404000b00501402201580462410444001c0e006031801d01c01c0e001c101201e40d410410042e000901c2c0d14171440d4010002814200c0c41d0b44555141c002c010140d5109010761465982042222015814001910401ca940b20009000c401c800c254240000c8078928106640ca4641484080c102610400700c65025920851001a1981c807901e406031030181803462075403040d60726004000c061b0329a00814900e180e0308840340300310300c0040c0c00080c0c01409801342c0a02958804100a0000ca40142c001c4c1a0109016220b5452008502007403482d4442401140c0e08480e410403041c1c2000711039410b840c8010341c20320340c14030380c540c8400304042244e00a003503a17001e55005084820350150480d020b0054680354070500441d524000200d00c07610f02c60700c800682040705a01c0d1074010726105001c900041d00b51607040030b00104135910001c010b011a9041079102d501c0f0040415185d1510340728203011034040d146000c9403220a1004520b401900802c410455500c40a2480000e00e030740f07100007000301d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 395869559 1250 395868309 395868329
    0x6050a09061d06090703020c0a12020c1207140906010201020702041406040b0d0215070309033005090916170c03161b020409060603020904030903030e2e03060b04 71
    0x1450041c4007052402000c1c9031400c80d020810a202494903111305095000e8050700f000351340d480041c0500d03450400380c0c45000c0e140031401382510785030303550110f2400b00ca808201c40700890002030711611519940e0350311400c0c0401c5880441c00542d4180941007a6000b8014000103081c41e0054012405640c9880312050003074289208001281c5090720500541c01d43c203541001b1400c0040c0d0200341d02010110706a40030050100701d4034101449a44007a01940e40f03c254101e01f81c0030360f072900c024100600c141a40604000e141c02c8040d034801d60541e40d034036100410310001911040103800340800404c1803078040000030300344203400340802402c19000b2801d10003801c1c4e0f20719101c2c11181355805401c1200f81040304c14458220302e10f4080400c103803001c0d011540082d003d0914501080100425880203410140420401c814141c004e440081201c3c043d0702c80901c008940001c0004080b0a88907074601c0141b54201902e07101030541c4404c1c3c452070340d4240068200c1d115041c031070b01074103e68420321101e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 395870809 1250 395869559 395869571
    0x8060918010f1b0f020303040f02150c0304080105060d051b01020319020606030c010c0503030c030a14010909020a140a062610080d0509061b2d0118020a0e0a06050a09 73
    0x1040d141e4010300c91403491400a400d804c00c0b40c3d0094507440060000b82c03071004612098070075541c4d003201011003404107010480c1c1c1d8180302048292680c0240c400e40c0d4280d460300300090030307034146a02000803107580900600a0380550340c11401c0205e0341c5c2e401ca14114401401801c0c00009001e20f8040c0609482d001001d05d031804504040c5000c100f142540d0400072103c1890300010000070940e500100c100c10000d40b41c2e5218401e480081003415507254020080b407000042741900c4d94880d0210b50700070340340041070319200d94a5a4a00100704031440e0030640c0380c0c00401943d40f14a00c0c2d102000d2400c20100b44002070030600360042c0c44160341044000c42444802c0188035003c0044660345811414003038288007140c2c0019509004418242c000322003945010354540d03034144200705c9131840005c038103503560411003c1c00a0040310081e03000c6540d071901e1b00205681500c42c80d1401c0c21540208000402818001d00e050410f6026152041203504c440d00840c1c01d5690315080070240c09584400a00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 395872059 1250 395870809 395870831
    0x60f04020d090b1e0901022d2203291902040806010605090a0f06120b130c0305090c09060906010302160f0f15050402011205190207080a020609060708060918010f 71
    0x444c8002610981d032582c81000080100c1240c6d0189a00e0900722084586007030350551411002845040b0f007200c000e103d944220424034032410890303001c1c0c1e4003401080c5e1603501e100712114424000b008130680c5510705c240016240b54840b9803040c68a00040e030025042070f42c0e40a00c07614202d0f0a130001c9006c01c1c0e0100d80c040b90313401c0c41d8540c078009051121520841c2c602e03049010388031000c0c00d103003c0405611030102e2112074035001c140c415940d910700f504100003244d00780020010841500d900a0501900080b0041031521b04032190140c200105810525140c001c01940294051000c00201120b649050000304040800310200e44e8052400035082481c40c0c03802c41415031889191020700e928000a10000d40d038000105030100c9a03c110001d10b0352a0b001c0e022103600c8050f05080c0348507000180b0b29081100e424040c0410034030603006c40c0c8541c1c45101405480741401c41d05d010024400e03100203061450660b401075006814103450540d01d80d0b045140c1030a445040a10b8151b0350303210729181031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 395873309 1250 395872059 395872111
    0x501031104050601091212050c16060908030705070b030411060304030c0308070815010c150204080307060606030504020105180a030204020c0d020601050603070c11121e1203060f04020d090b 83
    0x41d03c05401d20309910b0540c10074128288800c4629405040d401c00074540d100b007203001c1e078101d40110303801c04c044443d4298040015880841c10b40110400034400d07050010302800c001041c0c90f58076034050050050303d070510725003486a800050003500c1c036488a0001480d10703110100114041d6000b41c0e03460522003000d06000c0d0890748082e1072103040002d000304004030100320110b00c11441c5803d2070030844011190801032150510707100d04504581c0300040004500c0b40000041040a00c41d000a01c80c6a0380d943c016000c403541154041c0c04990100650018540000440180d40c0d100402c8500780f15104c0c1c0201d002c80c0c0220704503e100d68400d0710141c102c1501000313210b006203400c4501c40e14518011800a00c0043e29105c018044007500030103041680e106c5260310b40e844c50803407c072000c42c0c00440041c10b101d4407000c0c00350510f019010706003501440c0c8d00101d070700c52400074082d03c500302404818003000b0750141c40e0705214a9515010040000c50f1413499600561302c4a680c40ba0100c4442d242e03070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 395874559 1250 395873309 395873311
    0x70807030f090e07050301030f30140a080c0d06031208010305010f0c051b07120605160e01050f03090312040b09010c0513140607050d05040612020a17150301050103110405 75
    0x109005203c0810070f0040d44002140d0640ba4420746003000d5000038901100301420042548501c2482084c2034102180c40c044865a40d0541d5a10b020315030401110030800e502c03032100441d000803080b400246071808180c0c000c0c040c580005500160b101e5882c0c59030714902089144401c000b0b1500b90041051040034011044481c020040c100a04001c00d10060560300c075a44c0c0c2901c48000c109100781103520140001030003044c1201030740605046030b00e0322400614044801c008002c0140d0245a4414030401c0702c4440300b00180c44440c81c20101500101003a00010520728803844200305c1d5070080c521010b1401d00851045010003418148003030301e2405c0d980030686103020011305100d00c0c900f141010000000300c8082030702c0301c1040a011808252584150340d8040d0091141414a560140d8080f0040c81161031079030750500321300c0c442c0c2030074020fa00c25200810005615180d0100201d580340c0801600300d1b4207040303140301e03580803413000c07030300f5a0001da005031511501400c1d00c8556003004e018403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 395875809 1250 395874559 395874569
    0x70c05030303060a0323031804060e01080601061d031006050a06180b0c190c06030c081905070201061203080a1401030209070804020d0204051533030408070807030f09 73
    0x181d400c40c0381440100741140400d01c4090442e0300c95120070303540400721501c5c001c10b9020780d00c280c80c0e81e0402d801c0840686105c0c00c81c22030180385000b4002070320341031040300103050302e00b0b01380070b4038040e46081e408035180e40381d02d00c40e04034aa54041e1502c000380c0c0e0070030a0300b4800c59280c1020480c245450104020040c041d44141c2c02c0c020548003600304030386880c85080580d02c81010f25511841c5401c0140c0c40d0214030300c1d1450310348003482010b10a0140a942203c210760065409200e80006a4011101c194081e14012100203c1c12008004070b0615041643e0000961000090442d0340349803482086490000903000300305032105020b00f07401507001d200b2031010b00c84c902c0c0c01c0952450b80071580512004014508121225020804654410b4a00390700a030b002402844541403d030340e12000d6440901200744030325000b02040c55005500e81c5d02c07444c0484201c1e2510703001c21040a180d49180c0c4002c10441e003600041040e1000104000e0180130b0490195a40a07118031000d007019080042d10703002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 395877059 1250 395875809 395875813
    0x7090b03072f0304170609030f0f0a0c020306010f0303020115150c0501090803360316020f030102030a02090901060c1104020a050706050a0f0f0510060e01091a070c0503 74
    0x1009400360b005400490707482c1d0703084900e40c44420402c035840c10305074681c0c0c4000568000040e0010317030300b95041a610480550002030301c000b91542d08100f5541e20501c05401c00303901d01801104001c0341004094440702c000c80c1494041c110190380003072b0404000f604a20707003c66100030706005060382441510103854409080f020702900386500e07081300e9051402c8180411180c600050b04000c0c007900407102d20307540a40c440d40c50741000f44010204005044112400c0c3c0203040e40e161301d4150120300e01e0040e6048802075454014094017030241c0c801c0000b41a604032002e18905015501e0903c0254480c01c2412401612250200100803904006a00072030800c5500c005400c04180f8060462907007801c00c4800682d20211030b1015601030046c820060010741c80c0c181080007900c9240c10168210100f0442000000404c2000d00c003166000c3d00e102c0e0b84001c4c0503906000e440e004000c2003800e41c03014100350651035982e43d0340e005200d0414440694206010840f41c04100100413400003621080340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 395878309 1250 395877059 395877061
    0xb060d0908030702240109051f0321030504030e0402130e09010e0609070308030c030a0b1305090c040911040b0d0f20010305150411040911041d06010206040f0615080607090b03 77
    0x10700d17255905c410702409070455503a0020940820224281c031500f54600d5820851040d40d0381400720024252800394210111041c600c1d881c018424030071207101d6030345034541da0404515042800700a40025510710341e542500385002c20304050a00751103200310307a08070010400740c0c0c82050a50401078080c03c4078042c0d60003c10240b00240101d425240e12189128840d074503a513510b1800c13405401c842c100c00703802c26094100600c11441070b4210a214040c503200300e40c40e002c181e03002d0000b01c84015001400004603691020441c1c501500300400740d0400a0413200d07021116210388115040704c40c011196005500c480b04035a5280c90401861840709080401591400d05034452155401400345840359540d03046009000780f1050030386010300390343e075410800e007046685610b55540c824040c01d402a00210414a070803440181d1041c41040c0c181e021702900d0b1900da40744203c00511080480e0120303101d4030b0f0134260082000f05007000380070090003403c503801e0083c00a401a08c10390071440400900304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 395879559 1250 395878309 395878363
    0x1050c01110408010f051e0604061a0a02011a0609010804080417100b0117011e0308130e13030207060f0516030f080603013e121e04020307090b060d0908030702 70
    0x1140341d071106247d0030300303202c180d60310300000400414076070b0042c082c0443e0146c8020800e82e17070078015005556040e002004001d24030005040895184590943c1c05071082001d81c640b544900c40d4280c00c28403862186041070340f00d41e030041d00c14018034480b207070301d034401019052048103c3c01080380380c0c0002c0c2052000f8034000da40012041a050140b4051426405240c080f19102020880000c64000c170710302d6110400144021040603a0b8030401610080140118900721070103005244100d0b41138005107404c03464507405860b90505d004012061000038071100d42c09044400f6507100c3c1510940d203044030b0300001940982031400143c0030354040e81c034000f0755400c05007150680101e07084500101501006004d09114020708000215030a003200c080f4401010350440140b20340030305004c41001c12102000c0f420980c454104450103507165020781d104100100450f880b0f0381082d00c0140c00b04e8580300003c81d01a090710b401c400e007210018400000c100c01c2603414412850500300344d4405580e201480 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 395880809 1250 395879559 395879581
    0xa0905060f040203090a0203011b0f02070e1609150e0109060c39030b0907050102030a0509091b03070e01030f0218091e041208010605030112030e01050c01110408010f05 74
    0x8807000318001c40c0d000000c0b9188140c100640740744554020000d0203c0c0f5816a40c450010b1400d20300342003c41d4600e6110501a0300114902c0b0503209008a50b60b01c0d56210100b04c0d07030380e44c0c0b0b901441e028400307030260200342c0c1030040c001154007841a4450740104107404000410140841d40800200b081215441c000240070040951034041035452600700314105003990940d80c5246440030302d4184403001d0020400100c056280c0c404c1c808601992400782d610740059880e40710b200480c0002031010851004185010080241c0090503000d00b0a4807544d2052403c1056000f607440b01e02185410f240821a0340e814014070001151695055040c01c00307000003503c003006000129803294001600040000024040c9040c10521403001d00b03400b8205800c00c80300250801004000155084002041c400d0044003203d0403030302101550310481c0f11945040340c400100400003410400304125080f1501c0c000d005801010301c640d2101c0755181d181c5001b90303085541c0c1c80d00030b0040504020804c0801120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 395882059 1250 395880809 395880829
    0x190905030a060509100f090204050c0f190e0a03030206340318020307030c080d020606010e1903060c02070f05040b060a08091c0305041103060103080a050f0f0f07020a090506 76
    0x1c040342c041150f4032054006410115078000c92200d2034589501c1000d51a0035400c200b55041c02540c0801160b240c0d0ba405242901c9016401040e00804000c1d040c1502075500d0220348020307240ca404001081c0c4400056080034140c3d00660040c2d00c407a06005159214940d03070b0112208400818008200940c0706804040081058400b89981d821020034480b921070401c411840d0300a081d42c01d655160300c1c0c14481c480703c50090000a01c1074a4604901a000140c1140545416161003045d442d0b410700300f0032821200c0d000c0710345500061070004000ba0007401400040d00403500504519070900e20604d15a1410340c2c00544a01d0070045100c540c1d032182030031598140e032140b508a10130360380c80180740e03d04080d0303d145180c0c0c80d04500e03051044a0781a400907001c3c40c0328145000d0890803a01c201541d901081c0001351410400b00148410680560014a180a5822111800c20703e13074208030310054010b83e400d0403c90704005511801c40c41d110917014003070007500d48204040e05142c2c02295000407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 395883309 1250 395882059 395882063
    0x8030a0510050102101e020a02060f13020306060f03010b03010e1e070f0b0a090e0a0c09240302031f0311030114150f0114180307080109050a060906110c03190905030a 73
    0x80d40351500006c1c8404039912a5001d40303030380415507440207101c6000703540b1401211013130701030b807424804a80095820405a101c943d0014001c103a181c56100400107400c80f2a21800c0d815980e0703030f028032034980307007805225000701284003d00040100107080c0c500c01903050404201d580c2094405101200410b248501a1258036410356217030025441c042c0c0d100c01c0d264000340030784124031041180c00d100743d40005803951100e03581c80d000c0f03035501c4142c09441c8000d182039101040d503141c294014907109a000e1588807035a92501c5500702502c0d4062680d541c80d0390819075140318445c502d044582802d00401c074030515100c0d03000c003440c900b600d4084c00c00d40c030342c00b030052052102d40b05641c0c003a8425180c000c491800c03441e81030341d13440c0f07141d003400c08017101d5070000e60003401032910001d00c4c0d60341031080300566038010000d000b0400031990703504000c0070a8171080741e0869031070101d450301010300400b0704141d0008400440c2e503190b40706041d044009521026004208803000140f207551004107a45103250707 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 395884559 1250 395883309 395883311
    0x1a16020c1f0203071407050a0b040e04020d02040b06070c090e031611040f050106031d0303011404180f050303040c05030606011b03140a0c020f030c211908030a051005010210 76
    0x101d804441241103108244000c2c0060500d8091a0300c403510209020b0100ca900721604140b148c0d81b1900b8212a016510424501c06030b40400500507090501d840c1ca03110348010070018a032440507000a6560300285400c1e60380040c0311030103001e560094410301c0c40000c000c1005605152202049841440c03a24400030018108507090038450344460300001c50b00080c03800144155a1101001002401c40d130b00e80341d00781c4610306002680c219010045a059840c2040e041020301042001d1101501c201c25071083d802e02c402c0920008203181036003648509104030040c40c0c4c0c1e8205424400c1e4449140e8210034400d030084020311100c4d07a0801d1040f1104c9aaa1242c40c62160b20f81c00c0681d56844d00702ca8541981d200002d0300a0707010b0b0b00c0300710f185210b4821241d04900ca4030300c80c01d140d41d8880610754240c0201c0c03421100c071058080e903d504c403030103d100c008680040b664111900d03a616070101c0110340904001c01440007107040c0d401040da100c0e0040121518030751030080001d640300d52400d1406402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 395885809 1250 395884559 395884609
    0x512030405010c05010e01060909120c032c04021207080108010c0503010302040902030307020d030207090e061311060d060308030a0f050f06011b020909060703050c270109031a16020c 80
    0x40020f406c0b0b96412100d1030020407419a44a03903a10141c0b1500030308503640754290201400b01401208501c1840b41c15070b0f111400000e403002040d0b580070310070420041e40c6924070082d20003a1703100e000030000e601140114070414145081c0240c030075601030300452030030f0b414104244225544003095a0440e60110307004140c40d6005e0010a0840c4103004002e50050200b204030414150001207500c11120315003403c0001c48c40303030320f0400c0e11003d050301c2000a0482017036003000850070440440044180041c101031420201c0801e400c221510743d802255031b000c0203c01c000346c0110754415601040704104050003c0d181810100c40d01d41001040310707050049003032040e400d010704000a0050b49501900e14055410440340255540808076a1f1200103400c0c14006a803140030101034600300c01c45031101c10f050302d04a81401c640042400d10442c10001e101c000003010511048044007504040c0072104c60301e06100007100b00a108042c144000c0d584410444006516628600c1c045900c6042080c402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 395887059 1250 395885809 395885813
    0x180d02040204171b03150c1b0706111009031710081f051e0115030216030c02041109011403100b0a1115040305040e0a1e06030c0512030405010c 63
    0x90007542c00106000c424561101800c143c00103400c00346400180d000b0384169201d1080658980e607014043c1100c48151000c64001810040508542070b90080c2188030201e01d030400c0c9245c901c10740e02941c002248894004034090b0280402c1c1442c4000038000e014280c1e0b10788015050b24042003002c4404d40404000604101042d2040006403410078180c812035a4036044d040c2070886641c0d002c580d403901d0240803542500c00c80c0840c0c003200380e00292101f626880d12207450324500e550700034401819002c0214152801002d501d00ca078131442501e90100201d044e0041c0001c5645069485601003c200000c007110383c2c200c10301005031100d04100590b242e0300c152841c1003d24050380002e00604000c5080d0300b00c9900300c031030281040130b208220f6803003845440036452411802d440c00340100b80100814403034400c248031150350000503040080b85080183d401c90301401c000d000704480c8a030b1303030726018010401c0d00b0b442d0700010b1800b1204180301c4039000d9010f6441c1d115070b12402d414441d1100c84001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 395888309 1250 395887059 395887061
    0x83924180105100e01090b0102071707030606030f060c030e060c0a0c05030703081b12040308070315170f010b0303121009050c03100e0403020d26010f06020c0303180d0204 75
    0x89000c4460000d000904090811000c040b00038091000807138100310020840b81ea8520800d005020140c0c02005840c0c6009652010300d820035a50040c24000c2640c0840070a440f400782030300840c03165038083c400e14141c0c1000000c0f9103820451008041c01c1080040c84034800051503500070004005165941e840030100747c3c0e140c482804014550300003c14401e0516030000141d600c41d2411450b16000e5040e04071040005100701c0e210841c06100980c0810b001c00e20500c1c4169110400d4140098106c0e801511012120610b80c04600018203c0107200b64603e42445580c8000001a000307115034100c3e000061340340e02980325a11501401440000c1115410503001001810b215000308200e040c46aa0942c407588111002c107030301c03c1003d8000980c079070002c459070722558159018100a500592045545080c10802c2c08009603090009043c4482d40c040c0041c020404040036441061602d00040e06262401304100c0c0700303030003e000203035500003050340103041800111000d00c40300d601480024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 395889559 1250 395888309 395888341
    0x120317070f11010e01050a0e0f03040f091104050301020315010905010906020604060509010225020915061909080f010207060c0c120302090607140f10061a07083924 72
    0x94445d40c00c1605100c40f515582c0c0c0000480242c2c14141d582080c0b18502c0160f4038822485030000d01032090380704214640306030b4081f14405880c500300500c2e03d9900c00000e4260f800a0350508c1c2c0d0030740080310b080b88071742e081136400c0b004041c00e007881000c6516004c800b0703454560003070020386450703151400120080002c1d81101c2d8490903144068007008211001c0500780794170820200d006191340030206070b080040400e1002c090f00010700540c034042d807022102809864151408003809400b40011806240030300c161040c1500c014001a11400942090802c0d10102503454003484942049203003c601000c44003906d035551400c01580d80c00480c008260743d4400c0c1d100207021844074400a000c25013011861243e214005012110340c807501c1500d50381240c01a100b18010601d02809582004110710050000280502841c5040131a040e1270082c40c0b81d0b43c2c4c24a00a1110100200c150f00050080105400d6007061300902e0304000c081a031200383c80b00f5000c2440da07800040b0000f1b86140c0b581e0380d82 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 395890809 1250 395889559 395889581
    0x70e1201020c15010303030c030b10050c0a0b01230405090d0c110303030f0108010e0f0319170906060a060507050d0804020d0c0803040501030c14040e04030c0c120317070f1101 77
    0x260f400e860700c0c00e9410803209080c002140003c5c1007920150181d4420300500c0b100300700081c000500300d13034080c10580781648007a191250a0090112950100310054201030003420380031000f920b10f03040314681400c00c56441d121240f085160005200c0004000a80d04000e5445800d001055400d40e003001082400d15540107a8503120000800840c4185c649805040b541000b000b485002035151807681c8406240e0401880703540240010340c040c0e9003c2e0f03000b005c030a00ca4204003042d100b561600301c402440841d040c00c8103501000503c491401c000c600381e40288101e203403041c14602555151034a0344541a0503c04000c001c0000c2819965514070911050340d0103100c0b040003640c0c60902c152a03410601c0f4040c040b0703260049030707424135003d84c2c0c001144100355440c0524207402d00001c807842c2c083c05442a0200650214071400084404201d0400340440004c01e10030748031185401000400c0c2404840705221204050110f6a608101c032511a200c040c1821040b40c1032101b000b50040100c8414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 395892059 1250 395890809 395890813
    0x3060a0e040302100e241008010501081b100c1203140f04060b0a06211d0705090a0b1c060e0304061d03030403030504090b0d150b0103060905070e1201020c 68
    0x41c00101a0009801601310b150b1420600c840003060140c146c54405414245900c0d000030140407403443c1e0100c100035031020b4103582440ca070684843c00142114426001644c079940050030145141600d05011414210129100010032404510042c611600620000d040319002c900c5146480d00a402685a0240540d291001443d098232504008038007a28242d454038502814554113061000500c400d0f60380c1910781403038100b050728440000c04900309540b0300503551500c503600076445a070030496906401341d00400e4584e00308010464015030281015508910b0450b50020035202c1c002c1c4424105002e4032120441d54032810550b000d0300754001204803600001502040365900000d403605c41101c0c25512048105442041c190340748124007000e00814024403042010207003541003102c00810242503600d145080b5580c0d40d01044d030f401c42d800150781c1c448074090704030750f03051290300010101c8050a01c120f0920034805491002c900740540e014810314103a5591141c1b00350112a01500d08200b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 395893309 1250 395892059 395892061
    0x10501091a12070c020f01051614120a0c03030507091508150604230d0b1305030715020c0c0d02090c070f0c06031b0f0206150d051b040b010309150203060a0e 69
    0x190050514401072004ca03c140d010311079481b950b511580c151440c0d805030003002018560582c031040309203070780011100f44c140f0409000350740000040e4003504145000c2d455009000300c4500d009402d8890080071002049900c8404100410903120b0016a51006050800c00341d04c9244154000d10388030780381c13a90040d0f0005400606003510040b545c1d0010f51203403130b62008500c035004002c000350ed0403801030301d000941004a80c2101c40c2c03d2015074024481c500312860000180e41c4c0c284e900c0710034401110242c0d40403547d40c1d40130109001c0303801d0300081203c0d101c101980c11342c002003e0302800340c5270030590000841d90f44100200f148088501d650041102c40b2420358a00000f0007428101c600c0c041ea21040c0b40344840240d01030580a08514401d070094521582c6480d001d1510034544205c3d00e43c85010100c54002048003880b28803040a000c8514029501100e020700081d9402d007011a030405140940001c040b4a007404032030884102c814003d80c4e00e842300c03000510510015000b0082c2001c3d010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 395894559 1250 395893309 395893321
    0xb130305090405271f0c050c0a0f0303060503031e0f0c01060905101e09110706050a0608061003150b040e0f0d030b09130201030e030d09050a0218010501091a12 70
    0x84411080e071a00000340c1240d14044a03900c9441304801d0058440c0e01403044001901c4540c140c02010000c1c0047c41c20300e0522035400e0540e4904210401d05540310390400c2190001c5c59418020440a450150005d5244c030300000078001645043d00450b81001c10045000e00d20203400504a07160342c0c41c0340d0000c0c0902070301da84800c0001d10b025540c950058200450000d070451400f04c0525800d120031082002c0d1528001c0380f00c014000c019a0308580c1d0800304140b0000511612450340030f2407010000140305400c0400580c03600802519100908007868020000544224500d4a00b209114004504061848040b134003408808000d003400713000304000d00722484e10000d1083c4100f4a20f6030144003048440c400d00669200644145814600c1c503000400594002e0304240c0c0c448194030102c1e443c20881e120044103d0300400c5003203c10f600140c1000e0300350315110300d070b400c020050005041455450a00081c0482d40e9601c05d6401703c2101071503402030324001c1c034152442c01d0009103811000c0e2800c0307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 395895809 1250 395894559 395894581
    0x4021918022101180b0d021c020a0b0f1818090f07060c03090302010e010908030f04030512040f180e030d1d06040209130f02041103061003090b130305090405 69
    0x40390a01800a4210031405000b07500031900d20b040320301c07002451180440180ba001e000d4401c0703070a040d4006803229204030050f1607603d01042500701298461113610854030400078a00b10541c00f4001c402014425240048402c0c81255101c203071b203a0ba00b00c48903118501060f15085030044160040c0e10180811041c1827000c00ca0f4a8402e07141c5080d04c45481e1108410f80b4440030b901c901400046d0500c0043c0300550254001c00c03041c100c141003800240760740e0300c5142e103990b000070100d401c103840110707007001000001c0101080c1b48143c0700040b401c1604102c02019403507003503c03507181e0556441004041422a907809050600d9000c02580da03240031544010010301001c0600440991402440012546c00460070502a584c01410f03c00e50f0344840b0034110780b100100c10144d884004441c0b144006070740b02e10400c60440b08124100d40c4274a0001d0030020380200d0806000241410300d809440019050a0026844103442d8100d80d40c000c25400d04031540c0c01751038500c0740c0040c07404050220f16900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 395897059 1250 395895809 395895817
    0x161704060b180708070f180f08010b0f13020304080c0304120b0601030c020d11031b06220b06101e0804140c01051b0a021003060e0703050f0402191802 66
    0xa80b06180041032880c810b031042c40301102c95070001014078001c592100d1180e0500b510b040001c0c86d240204213680e4050340c1d08035200b64461440704000d540100601e081c00e0058440c813600444080d08020340c01c9001c0740003034a08410407171500380d00100140800000405680c0207642900450f61165121a180c25500a103144159400032031080050326940c4030f801120825611580074006a40da0a6000e542c0c14211170001c3c000fa000030300c40d08141c10102000013104c125150010201c60030119071041120b0840500d00ea2401210b0050b80c01280010315203a410240a5035058083c4000c96803c4a03a884040d0400e18015040a1390310b501760740c0070f41490b00a5014000c54070b622075003217800a580d0b10300e0100c41e50100b0418030401070f00c1c100c44010703401d1106101307080d6185050280e001900f007a82020031407010a40d5514103200c048040c584550740140741d81403c003d98181182c03004004840200024407420021108030280100c80c608070001700400300c818142d002d10a40a440a500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 395898309 1250 395897059 395897081
    0x40302060105060702010203070b071b05031308010e0706050f090901080f0d11190c0e161106070914221e0603020a1e050d030302090907080f16170406 66
    0xc9004000306040c0340100c00c130303150654160020351600c05e240c0c4c0c80003042e550003003240090040010582c1341e00b8925a440618051107600511798450201c60054492303100303500803c4507070f0701d404002070b11300c0c3c0001100341c26144242056901d99490a6200c0c0e40703442605002c1741c204100308000182000001480000a00d030442600d201c3c0d02210400c4500e00c15070800352074507a114000e80c084541d0700440b240030050255008440c1182c4800d0840d411080958004c4200c2c47c07890303e402000c03680554215460203d80000d0921030801e5107000308003001031b01800c0d03212401c03e1200020769a0f030b80e420098004100c0c40140303e41e0412804c040040c01d50011607105003455943c40c0307810303580c2c3e84190016640d005000c2c3c8005410604d88a04524011207030800c0005100800f040555515411048072031003030b6805a52603885405001c01d201c0040d0000040c40900018814082c54445082d40d01c01c80c0242c10880d01500240e049482c2c0101c0e01c41140040c0510060105101190b000000c00e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 395899559 1250 395898309 395898313
    0x3050f090409150c03110a0516060e07030510020705060606091f0203130902131e0320100e0a050103020d090807060207020f1f03150302061c1a060712180e040302 71
    0x116100c1d0030340a55280d50740003254100100464030805018070080d081c07200e46d1442a080c1c49e00340b03540b48000c803024040940001da029100400410504010303a00c41c541c0c840c0400c1d42000480d6540ea070b501d4001a2509120712008221000c0540f1003800c0340c41050301b400c43c901070801c900c01000c0c0d100d03400030691100010240f1400b10306121503000f218050001c1d0b148280565251144840704484c1c0d059040c1402102000c000011841c2148424008050020030502030403e09042103090b0410704600802d00614261140ca03641d00d60100004868003070a000d41e58a4605103503000410361300c04014180140400c090f010300400da800f51001a100741c1380da03001d21010004010000540a4103007034610390064007090103502c240c0185500c0302d03115080c4403890f5101c1e800070700d40d5005034908030146810004920900c588500a103018960f90050820802900c0f4003c211144241f070400751070389001c25035890202d84211841c001803142603c540036916110655648078a43c1954140c0044c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 395900809 1250 395899559 395899571
    0xf0f1103060912030109050403031104060f080a06080d1101022205030f0610060e040603060501091b0807020d1404090c020f06061008010e040203010f050703020c0115030c0303050f09040915 83
    0x1c2c000840d00019200c0b02202803d50b071920070b030728010301002001201056212441003000740c1242e000341010301040e840d54901c2400341a801011400c0013060859628280041040340500204141800d2402c91400a0395158655415806441503441809900c66181030010300c42d0100031003642034880c1201580c03d001e4080f04050f6980f070058800e0b65a4640214040001d14011f000c0074281500c068400b1400554a40f50071003140c109070311080c6419115166491401c4014200e100ca00e1090704280f951400c0004001b5683e4040c0032824081c46000700d402ca008143e0b0009403001000d403510305019260b440c400c02901c0e080b0b040c000103154420078020481d18a000c441e1816140300913510002c05038a07047c1403602d2820003500c1640c05558074112200501410700600e480381c0d510380c6001da5030f40c07241d08600c0e0031510040d01d507500481c0b01000600000d409a04000216030301880c1c9035441d2801c601201900e4854692040d40c4176240a10300c0c006c02c03503a0b403002c00c03050300485020068 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 395902059 1250 395900809 395900821
    0x30b1e01080f100608100b070803061201140114010504081227100327031107060201020315014b08090703031110020f03010f06050a050904090f0f110306 67
    0x840503a000f60300c10044007402e104d8588103501c000d9100b0350b01c601507640d00f903032080c0303203002540400030030750b8262800802c01410b41007440521050040400c020072101c040b881c0f20701441c0d60107001e40000c450008a6208641c1c2c4210143c0b00580031076001c0e9143c10101c3c214650701580b059640071008246070f254003402142e4000c0000304084090122681c2c0062183c0c100c00500b100d1400c0c02c500d045070300901d502c40700550030030050144281c44c1c10010b940c486840c43c0c83e00f00d0310b50101d81168010000c014000c021300a660110a0083c20324104241981c0b80110144080300c60041030140d85c80303100303486201ca4200b032504600c018a49261800d10710704040710300070b0003141c1c9015240d11684040000a11540807200e6103400074040e1541083c030072000700140e91040196081807034010006100110705c4030030a60041c1414103066241200e006406851400341890715449035556003c01c0d000d00824114000c4020381c80100b00258140d10710b0036141409407804060f000f84180c20001c0d031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 395903309 1250 395902059 395902081
    0x106050313050f01090618260c03130302030705030f0a0615120501020a0e01030b010206040b0910020f0c0106062105190c05070507050a360903080420060f0307030b1e0108 75
    0x142c00340c1040c189200c0f410b040e0b40103180c500c007001600c00201c23400c2244004100b07090014080180b107042881ca4494070b1070040620300305040e00030610a82000e171700c0302e4483d18005030b4504100d500c044042480d43c0e144054050713003103142d40701c0010241c420603900e04020040d401170a40d42c40765211030041286100044007141d162441080c09a4025400301e0701141c07454145d280d000072190201c421450990311150241d0300480d00309045c00c2c0d00807030041810002070003510050403051030720386440700090100e5584843d10b91010018079541c3c50114415901003a24038108004815040c0a0308000000041c83c6501c08c44003504c2c0703030240c0100400d041c0b8210302e0050032140348400e800c1c0302503000409150007280b4a0b00c2000d419440a02c0d81c3ca200e8024016640d04a00035142c54015140c90b0070070b1a0640c10341e0103c01c480846d899148801c0d40d4858041d90003020b5100d01890300d95450742000d40003005800d003ea940400d0301c001105140e00c81440075401e0340000c2c1d03103494954584d141a20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 395904559 1250 395903309 395903351
    0x3031008011848080102181005040915050f01020d140c0106050315040311030901020706030209011b0605071b0503390d1103120106050313050f010906 66
    0x10314481c1455070507101003180844403240140c4011030540a880c20b0384444180c15900d514550030703d1082c59a1000100d01180c40f4400a2440350000e6103802e61494002940c40c2645501c01c0c030440503c4681c80f8020300c1001900c002d030040080030002c2c07101045243d2125803480c0310702c612500c1c1048008105501c04114a41003102c2e80c2c490403a55040c1084401d1150070400a80310710790758580380025156800c00c501c074100891021141d9080c1030905000f4203d00340c9200300f0040c3e5108004841443c0d130300240308000c0701c2c114600117840f9401e003401203c20707100071400c1d00941ca03810b00780b04007070261542c07000d07004c0c10186c1c0342d040f500d0456101100c016488504060400d0b0000c0c032400f501100c140071401c0c240c1040341120a1050804a04003012000b17903c0c108001c0d51110084031009030300240f01d0003052004a0095040034074203440a4041e00050085104024010000c90000303001e00c0c0c0e142000940c0300080d180700343d201c0c071800c1e8001e0862100c15181141070204002c41102c6c504822 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 395905809 1250 395904559 395904581
    0x20c011a010507151a030109060b010207080d090506180402030a141e010b0f0403120306030c0f03150f0e032b0603080307080705070b090a1b08100b1504080303100801 73
    0x104804a41d041d03c04c0d00200365103803036041402c80c5e0803800f5645540030f01c1144907041c80340740006017081600b00020700e020f1994204030b415a001c0320f07507503050907040110f040486500f120419503c4610000803841411a561080d802500100500c10600025040b42e856030888004d8914190346101c0c038802c074800f0311136503500746c00e910307400501205078460014400b46100856040c50b086d52070f40c840000040010410000942c0c40d9000c1c42008815220480101089078002400034115280e08c11740300d449140d264019035440000780b00c0440c068010504c1d01040310141c80d210344000652039808000d4804041d002c101c520684a2085043d01c1000c0a45e40c018440d103003190340303c180c2521010b0026014500388502880544005440c03080403500ca5540340026007402602d900d441d000300319006817503841e2842d090300248500100010040e40c40003c0181c0030904184400100703c071031103604030210f9039020000e004521098000000c0d070203540103003141001c0d5035407250100d0885500d188a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 395907059 1250 395905809 395905823
    0x140606010c060207050102090a0f2c06010305060a150c0c0b030106141804091101020c031b0d23150c07050303010902030a020c0a111801120308070c06020c011a010507 73
    0xc0a0100b01c4940c05000d06501c2500018508205480003c08500407607002c141c2d0200121400d0000c40d245210211080c0826030b51540e60349844c08070444030000051000e41099550700002e40796030794130100c000081c505d0709130100040c10003030001800705842d4442030300d419002d41000a072010f2210300b00c0b4106d80c0d0f1aa5400000c14821011040550000d5032807200010300800601c641c1d55907100381216180318000350610313070845038006420000760141c0c0305c1c4280c0201402c095080c50700d030b01d025100e140440300302c20141c00343c0c90480b12500c40c94428501c80d01044100e04000e4000041c1400c608aa414030040d143e0b503400500c1d4001d104a0340c009040d6007090004016a40e5150080c5420491126000d41488200c40c00d107840c01c644000c1c280d40c1b54006000310b04c0c5a0500e0800039450100003510b080056052601d010b60045070040010100044003001072a50362140d12621a1903074001c0c1c040d0740d0b403220a403159010306140048a0000f0104407a80c40096018030201d985456101c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 395908309 1250 395907059 395907077
    0x402090d150b0d050c060a18090912020109020a0e1b030f07081b07031d0409060f0c090b0304080c0309030303090d0f0f080f040c1512050a022109151314060601 70
    0x40c0401c9401548851007400f0b00350702108130802380c5400040c0584580c203c0010a400142810f8000d080295001d10542e45081d00700c1000d61a0059003c003522001c2122030100c0e00d515240c0240f5030801d0a1107620341c8000320920402c80c00b000002c2e030141c03115a03504034960700ca03070413a0300c004903030741c80c2d0700c0e004d601c4c01c0120390b00007402a4031401d43c5440207240100100c00e150081402c0e100c0044044940a50b1000c070343c3c112002d2441205410b0000d8904a8091800c02c903047c00e0350300c0007a0000c0c2040102003541c0b5280740e81002140c91099016080d0b81c4c90b0b0600000d420b5407880802c95002c08104014003403440a845100c200744940400d44d601010358440310454400550003400c1519824030f6200003040311450210354000480055407194040440904035000b01c81c4042d04801805004028036a0400c2280a0000b44103a52120b00c142c0c9807a200007940c50500d0390b40c0c9000050342c001040000c0c0c0480ca20b07461031194003a44140344402d040350310341900c41104481c05404220614 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 395909559 1250 395908309 395908333
    0x30d0b011803111e0d03110a0b040b040c1403030f07081308070f0602010207030504142e030b060702090118060503070605071e0203070b13030b25020c030303070305060402090d150b0d05 81
    0x75004026130038913100740e0710060609c0e110001400400c481c00d50b0944032103024441000440141c0c0c100411205c0081e66410030750038002034403840744441400c03036501c0100d61007051000ca44219840c42020886d65848155564812600d544807442403000c00c122681c800a415170060080761046a131554502d071030141012034441500310140d0020760040d0310b0202c484103c40050300050000345600d070039421210442d5200a06481802e00c00e07038000e42c0c0038001640103844890710316041d50709041501074186400f200050040510354407041d85841605000180c280d007050003441103d0080844071155500440c0011481150500c000d4040c0d0004c1d00070401c051160001e4151030801d5807030b02144945d240c969000c0c1d20015148410010285402c00010701860343c03000c080f03803006d40054444d00ca00c4400103074503400b00500f04024151540f00141590399654100d4051b55002403186904000c2828110031000401e12503100c1903140c400d00b00d43c01d2a20441c1c03115095400302c014420030701c00b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 395910809 1250 395909559 395909567
    0x2040513050c0c0d050d0c09030c0303031e06090b010801141f050c0304140f090c04051504050909060117030403050a081602120303060a09060503030d0b011803111e0d03 74
    0x1054080b8205091240f100182414040c03116070080039510355480d051840410b00468800f29188801d025141c0c6d01000054494001d150440350142000261003031001d04c0c82c500f2143c1801203d600d1481c02c440402c1c0709509a00c00314401c903084c3d0381d0302c026a8a0383d440c8403400990a407040c1e4045620b8032103040844d4200c200c1082160a442c040c0d007001c12030341d0010729503005500b16114051a4400403901800c200d80f1618625030116000b010301c1c00d1031201003940d8465400380c60f0013407550102842003000f8240c00c42e002401d020f4502e041c3d91400c141c03143d441c1c804c02c2c058100e94801c88e842c0f010b15072000009840c00e49c0e4001d4060700d403010f4180c0d40c031a203941c440c03a00c0e4031754905192070003809071340c2e0003020107d40800900070f160f492421a08105855045400200400e407410303000340480d0b100007043d5414407a0100f4006641c06548005840c560701503241c0c00010b80454801104001020b00542c08582d01070361506203200c642d03030300c043d00c0808000e80160815000010400885d2107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 395912059 1250 395910809 395910811
    0xc1406070b060a0b04081b0102010203041e03090e0711011d0304090b0f040e070305010b0103060e040b0a0915020409060512030703051b03040608040b060306060a051e061909090204051305 82
    0x20a0443c0c07055881503140b000c1e8205a1190030380e508001400015401d072401a076158010034030085103141361540e120752000b40303507840483d103061740d002040c0d00f0940500000340240043c1041c12045140c020001485071301c111800030625401d0074071000c601d0f88a82400820103000f14055420a41002000700c0244140c0021503840499031101a03600d40300c51107041803040c00780d03021b80802410b50600b0340c20360320540d801e607042500d400300c100009080c1d400f02d41d400903800510643e135603d440480342c01410007583e0140800030f0020495584503003e5005104841e5210300074001c8039650740400034144032105024010350810000c1b040002d01c1030009021200c40b62035501c0741362480d000f00c985187c006400c950003160f403060074001031114201001c1e03070001041307004140034602540802d012255601c01e242c0100b800795040035000e60242510201a400901b000342c0701d9518685500c0407111015644000c42c01e0000b0109914415001f10350644501a0a9007540d00c1784549903802050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 395913309 1250 395912059 395912071
    0x11010926010f0204062a080a030c020f0f01150b03040506010b0703020708030a0f080a02160201052a0a0c0e010e1f1509080706030905062a040803070c1406070b 70
    0x1594a105000000c0302d840508080c0055659500381203542007015040b005800da5800c02c01416510007070001001030048070410b80c00c030320380881c0da01701241c0140d180146248200c101d5009039100d95480341c00561290009408003a03000c0c0c0704a0350741d031485006110959015142c0d420010060050102550003000401c1c484d00c11104981d0b503d03411142950000710ed401d00050045c0c04c0c188070113501c07803203454118141003021440c0c011001281c800d400c68034403000381170020214a40c01c0110040211239001c00110000860004402904988881c900042214280c100c6032000c60f0565845101c41d059800d00420441280c403031010781c0451424108980000480040700880c181307040e684060005010741e02c0b000009402d04544a080450ba90400310070186131203c50804148001740e0260030459800e0103840e01c00c1c8087c0c0b0030b0307442d0360313007103d29180300c040000c0014080d10000700915585000d16091400980c40760b00789a680c038046003005030f00150a001c0d6a0228981850507030b0099 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 395914559 1250 395913309 395913311
    0x411060f071401050a0605011d130905010905011d0a170d0e03070c08010203072109050102040b03040b07090e010608190501080c03010b0904081605010b0402070b01031101092601 78
    0x442580d1100341d80c001c0c0011940c038040701c440c4544400d001d024464200340da04c01d050011074180000246003a904140c5201d807151a504220070300d8452448a202006494101780003000c580d08144d03001e4160580d040700c480d842e045a107040d140c0b440703114142c0c0100d0311000e071110769281e4030740451100010092005e107180400c250100780d20303244901c01c0840c541c0400b0716168a518180b0194019150348603000b507900400070000b4007035110025510b01b6821041c0d013041c0e500780b20b544000500015000505662000402080c0e15207464040c61090f48078120340c014658a140d811503525209200c0c503908a400b00707006010b840d019464642e8400840a40c4400c8040100d1000d0140c40080e0301c60307a40c5030007003446a49541070038003404030703942d130141c4511211f424a030381e910350b251007542041c580300c06900f1035510411070290003600140360014015525000e490408922400d02848100c81456106842c04034a50080c801102110800702c1d1000107048581100d81c0c01c81c0410103000955 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 395915809 1250 395914559 395914567
    0x25a090108091501151121070602041d04230d030902042408120f0301050d0206041208090f120c060d0b030f031801051e0901090521010507050c06041106 67
    0x2007981d91079114000c0c11305540200e0003618043c3c01609089810031018000e4001f14407016028121948800c1ea04421000c015a81c1070305050405c000e016039040900402c41d4025808030300c2c50f09000841c051070145071f00700120f00e1818454002c6500c44e001903000c1c0c0e00900c00d2200d00c60700030707480060360f2400508045401c0304ea011620800c42d10420080d8580510b0000510a8503020800051501d2226071010318000c800b001c12951030005100d01c034495208038032027400b1502d4010645008225400741c10075912528580300b039594111250850103000e0070007400c040c0b8900300a07040d401540e5080940550510607040c441d15a0040744c0c465040d68403504035803401c0d101003000560240f0368102641c0c640c1e07070b40200381064408424100d0304000050280003141c2e20341c94402e500c506da00801c09503540031910010b8410100542c8080d40c07004182c0300800184404a0100d40c030700002e0802000340b6034905030141c03058015281c020201d540714000150014480d03101242c2c10041c002c14031814 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 395917059 1250 395915809 395915833
    0xc01110a0b01180b091905090309010926030408010c17040209070309020f13140105101b051e01020909070516150608030307050d0b030619025a09010809 67
    0x250180c1a00d5076000594031003042145c1c0e4038540314458001807402301540c0381c03480b0540000c20341c4082c0e000d0440b40b45c00b085101c1c21159800e20700242c0c0d2a0394070007900c0c2c59942d02d1300780d079008040901103207000c10140f01c00e8080706e21a020302c1510a0ba4010101d024a85815504400a0204d00c0040f0303005440040e0304c1085950300c0c40510342050f060f8001180c4000003080412010348107030f006a0250011090a0381860380000120100c0318030020328601f80007450400d0b41c0740031003030100410b0041c44404003141d200e8041d001404032000540c0c000540e911030040481d103512030202e02421400345001d11030009040003030380d2401002411008200305860b20f0515096070300a40e071800c00b2401c00200503164900c98059424000002c40281c01a0316240c45c041407a0200c9402003100c5550028a6148030a05210080045100d424841e83e01d0415000d041242004d060b03035444881901c040d00c039490741c0404402e92110540309440c5810510ba0398019201050094081d80840c000c60311018a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 395918309 1250 395917059 395917069
    0x61b030908030d06030c080f0a0b040c0312200d0e0103090c0e0f010f1203020c09060d05070603050709050a0b0f030c040915170f06010519170c01110a0b01180b 70
    0x3001c1000c003c001440c03461464051296601030b03100f00165084900102c1c0d2100d80425003181003078000c6441c429654907441c12031345405a50304000d0010f08400441445550710003210580030303a482001c507032840d40c10081d9590b5a07a0b800000070000d50411160103440d440b0340c00202d1858800c0b4248803a00b0b13268840742420460840380c10500e80030201c01089020401c00d46a8000c001e9165000c0070804140c400a40303400d403000045003e50712000101e8070545401c2c0417581c0441e00402510304140d00d4110090140c0001da8030074002404000021a00345804d040c480111280d80e03030428540b00381c420f0103900d1500010007111801109001c0010200490b0084116884a003280c0b54200d500f40303e14981c1c46044a070601e041c03944116041d00800ea000580141510022100f0340144a40f00c41e240701d06041030303001003100360b00c49103c0710303141480000c00d0150180240c84007083d61030020445640c9902d03540f4060464500100100300700b064030034038400740b000d9040012074011030f800c001c20 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 395919559 1250 395918309 395918317
    0x2703120d06081b030106060906090506070c12110102071502100e030f03090c15040e281104080c030c0901090b0d02060a0c0204050109051608130605010f080606030106061b03090803 79
    0x801e2036021021100340d40e140a00c41e40d070152220b818800c14071414120000c00350782b581d00905000b0400000e010040c000303103145400040034440c51f00c00e584c0903e0310b00360300c040d1104805580540300707000c2d0118007038a80c00e200110700525580108281e111503800c00f4042d2480082e00c4180b030004000180000c80c40703100a61007000e451005188041402c0e0038808220400380c00c1090440c414030061051f540e03524106a0015410300803071107602d208082100d03a030b1500c8007250403094a0040c940e280c507100c90740079004689600f030076201c000c4654014517460309440100b59030b104140000501541102e6032020040580190020141c01354a60200380103a0152020502044884039038804510b888c3c0111409030400c00018484ea0030000c030b9001903c0e61a4400320144905c0500145011010a0840680c207800400500c200d50791207a103829180c086000e1002c19001d041f00154240c10140596400c075102c5035240e00141c802d10a42c5988400c41040450400480d4100022500810000b030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 395920809 1250 395919559 395919583
    0x40804080d050705060a050f010306020c010f29030d020a0b09011401030b01080f011109010c050321040506010b07150e030d0e07151704080a090e010306022703120d0608 74
    0x2c0d940c3d0446801c0061400f44001d1101c01058202010444206000ca00b4641101c1d404203015031900803e02545001d84810460315110b240340155030084e4414502c06000c1c00c2c0c00680e121556840754105160302e40812850000142e0310403012040061243e0002560200f8007100004068689850401c55500e080c0d1056540031201d44c0184080341e0140b10301030540301580020040352111404109640c05000702007418851060817800500034240120f4941541404d00380003d079100d00342e51042c100d02904d0030745840c8101000132031440c4068044030400780d00710380701880d55007104041501600300381941140a000a100e22041c5000f1170080061400840016140d0b142c10280b02c8100c201c01203808034104203c49050194082d000c02c5030940040e00000a00c1d500d0003c8082079480e03a04e1075100282c0601c44200000c1880581d41c007803c01c92109040e0b04230b00c0c0c0700000c4d8079030304020090350959242d005003503120344400b20540101600003801001017041c590f0340792414101520f0b4012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 395922059 1250 395920809 395920817
    0x906020a0906030b0d1b0e04060f0c0c150207110904030c20010504090b1c05010209100e03101e0204061d030d0914010e15071a1e040804080d 62
    0x1404020540010703081c0c0c05080c961508112071a501c0001400c2e902c00f868011302079501ca082d1034526141c4c89410000035108015500e4a507060914003440100711102c942c14030a80f419650420a030f20440c0010085a000150701c183c403407010f80494001d51128004990040e1515494103468a8181c0207034425402900d400210144a051450800340000303604075400050640d060f0050380c2010541d020f0b51281e4000083c0400c10300d010a200040003050208085031070f503c1502045015001031115082c150384100000d0307500d910949000003520f50b0540c0c9608460010a8900b85590000079201c0320402c507030170441c81ca520300351308036405034004e174001074084001280d05884645400004003c25001844620b524030402001d640150045284802000020b4003c9030f00c121100d043d40d010040c81c9400b00590b060006002d80d000c81407c076409003007000381c4500500301c003d020b40300f12404655408440f181d405030443d80c00340140304480c4405d0900000c10b80c0c1030b042250743c000da03006490b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 395923309 1250 395922059 395922067
    0x10b130b1003020c03180406030c0e070e04061d0415110c120c15090a2f010e01021c1403130318052115070e01030e120f09060d090602 59
    0x1081c050340c02030003905401414010000382040c44000002c4848203400b4808018104c2400d030000f5011b08080c0e80080d10300c0e140e00e88081805103181b0304246c0240c1054a64041c0480f111081c0300540c1e001e0300c5520400406011844040c5e03812406159210784511f04c13080c0c03402e80740144002151014600503840880c041070240c2160400c21080c075011140d880315502782074800d104196180c42c441082c0004941200c0400d0348810100981419560700c0b10320411400e6805103140c4d41c100e803c8540040c1400030001408a65004801d19420900c0c103074054101c40c10005204480101c90b5601c2c00c0401122076003008909000d580558001c13100101d5007203051025003002814138651740c1c00c40c1310425600c0800c00095603020400ca018140011549840340050301d102410800e03907500750204c0c271041204200d04c0e0b44c2d0003018044148002d0f2410000c5a20385c0310031550320240300d50385140a0707404020f20300c90b0310300301f5000d0320100e40018840d0303103041007652049040d0380c0e1494084070b085401203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 395924559 1250 395923309 395923331
    0x913020d0e0f010605150304170409110d14041a15040905010b030c01050c03090112020c0109030801030312060807090504050a05030d0609050c07031b020103021303050c0307080705100f02010b13 85
    0x80a550021702e021501002d15022035814025144006407005000010000a02c010b41e5040350558008102c14101004816100b1401c0c0407258031a00070030111a240c0340d00640e18507460300416008641100390103c03012614914140d114401a21180090200024140b1566114010b90014600c50400070819138041c0c0241032400c05030b144094140042130103001102007000094403140c4c1024a0416a042d80c44220360000b8420b040713000031654286004181455004240c5034104e9100c0e58803071450201c2c0707a18000840d0070314001c1044503005040104500640c42d040b040d0001d024509640e810710050380e8103450765002845d0a00403a13203071802009078120740c0c405c4550003402c40b8461881d14015a40c02400054486a50070170940015006c3d025a4800d0341a980c200f20300c1d0124000c0d207034417410619951018244000c0c849c0c400c8210204014001048050840d8800350008010540050f025505001c19407201e0085640c2c9212001581d80c800740c1c540d48006000c0710004d000300140d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 395925809 1250 395924559 395924561
    0x1060b1c15080d18030c0b0c060a0c0504060c1403030103050d020714060f0726070512070f030f051201240806031009050109050607030212010e04080913020d0e0f01 72
    0x701203203074550036001d004000c05400403842d120800030625200c40907070b404a2808050381242d40020302170708420700300418109180c0004081c03040318102100d610f50345503c588415290380c0d0891000061003032004002d0180204000e0b01d42c2e502c5031300d11036201ca100303c0c0518510b42090740181c4080e404251070764042074042c801d840213845d64048084010420b68041b03500b0740704140a001c030501d0300145d66000e110803c4d04400b14200c1140d01188402800d08401e00709401c1104285c0f014016000155030000010003111030107030740199100e80e0003400f0344041e5a800f1200e2654030900c4002c000c800390040652803d18040d1000803249036031030070341e038540c0450005130703031124002e106000052003e159800127400b40d0908031408003044000085c81c140b400b40c010003000400c0c0e40304400500c100705405030060140b5100700300080b0916a42d80006ea40b804100340c0740075250350400c110500b19402e0242840c00710048901015250034002e6854104654000794a03040c55080520490310400003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 395927059 1250 395925809 395925821
    0x20a020c01090e06030a0b07021f0f0c030b03070b03060d05010213060909051e071403040c171b01120e0a050d09080309010801090f060503030f1207050406020d030e01060b1c 76
    0xb190000f20091030050080b030b5907005000005007d5510800006480604c00c0000d600700407190000c400350005020f100d0b50142004405411010382040c0c0b00c0040240710740315401040d18010001c01201d49030030b0b6072038507545c00a041650040080c8a81c600811024001014929112030308100542c0c5806d400420b40040c41c2c001c68241403c280511824a604001c00c1d102d001201c445882c0e036803940102510a0f135020700c22850454004070400007070000c0d2000540841c0e00390004a280c2940c4c1074001740c1c446150740c40c080810038803c551150703217521550b40031405881844002075101140e2080b80e1a0800c800d20894141c3d020304140c0340311a500400090003004240025030030042a040003a1416505026490469a550200161198071900003070003c05014065036501c150301c19220302258840c0c26005012030b5030070003040790b8034403600440e8212201c41d40903100000c4039040880241400c444003029940d2181c5010469a035204010400c50204444002014500950810075658 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 395928309 1250 395927059 395927069
    0xc210109050c0a0f0806030304080d0e10090b04030b0c1201030b0a0c050a0207030b060d060c080a060501020706050315030f0102030106020d1d0a0b0c07080a0c031b030201090b1b01020a020c0109 85
    0x1000e0228010240e000362180200f0360645c100701d40141d442c600030920311302070350f4802002c900c01d0841c07a005040e04030001c02988801914907003540c404042080c2c49144507032241180d00c0d1f004100400104445100854122980030107503460021014001e110000782a00165a04086442480443e20003441081901000c504090b810503040303050180d2501001d00c4040d016a18000c0054080d030341364031400d1440c0d40d100d00104540074008070024610b0354202c4068042910300a00030416600008440003140d803290b403443e10315603402544c074402966010500d40c061003804241c0c15404020300142d8040c1140c0d038010a900480007a0050400140030300d00c00000c802105d05038010341b1000c41780001d903118860016910f010145055190550a902c5940303107010702000b0000f040995490b0348103c0f03004030046003003000145030440b01d9014a1000a000c1404e1920802809402102030400810388010b8120445100800d40e070980e845030310b90000507001065448510b41e042400200942 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 395929559 1250 395928309 395928331
    0x702010c0e0906040c020102071b030c060309080a031a22150810181a10060201020a02070501110a0209010e01030b0c0315060d110a03051005270c21010905 68
    0x500240041401294060f119a0169803960704450106000350100e444046d0f100c5403c40c410b980309010707500790300200d010455a04844080009000b482406108511508100d0103490305144410a40c01480c840c500c001443c644001c03201000e0b074400d400c00c0803a034034001880e0a1480c0c1c100d02c4c0011144103a1040c504a0100c12051080240006070100111000000040c200d00000c02c00b0181c005280e10080c00030b141213f0b2440004088100140141d61002081b108103884480c00c1c0c3c240e008003558500142d009072000c0040d90704c2070340d880401c00c01e084182d0704140860303004118601426008100b006860100420400c00000074156120484000c040c1c250300340440801001c24134840300512800c008240f6440c104101e61054501015030100c09030360304402000079001d00303000c650040030581c1100c170021317072410203442002c1113403c0b0007203030170301d44d0141100510314190141c8054544202408026400e4228030b400024800516035014155890010340c0030583d480200b00706116 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 395930809 1250 395929559 395929577
    0x3402150109060f03020603041a0a020a1b03020604032003040909140d0c081c090b060a060f05040e10081e0d030209210109150605010305090307032001061a030702010c 73
    0x1025080b054000d0301d0741240e025540307844070708100484072707400c2e100e03101c0b410040c0040c054130f04200d40c018503400c807094540720310b089010840407800c084c0004010303001d40c00c08000600001d1040e03441507040c50015007264084d180982ca00e80c03541c1c20540041149544e40c551440074031000d4904a00d85000d40342c000c000d8943c0040004003281e441c40e800820b945004166040d0b072034130034000c4500c6110060030401c0100e890381000003500c2400c2d1041030050a0200e4042901c9125a84e800030004c1c184c1c480350b240501d0400c0300008440c004000b081940440100030540780b030140141c0d004000c444150340480100704e4041818030000109000c1403520400520050340c45081c401164484011001116082c2240b00381b405041151401400c0407403190142a88441583c0840b055400a0381c04102070f540791201c0555911801001070040303420794080100c14041c500308001400010380010500d0382c0d948000c00640d0000ca070000e13640c000003108200f04070303a0921502007000940d1800c1210 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 395932059 1250 395930809 395930819
    0x50607080115050306181305061312050d11030403091d010b041401030b030706020d0215090a031b02030a060e0c150306310f0b060a0c1119080c0901060c0506340215010906 75
    0x542044603880e401331001c00300718601c16000d2035000c900c04844100e1026500c0c031b0036190042c8140f42500603000c00c00281e642c1c1c0200c3d0001e41a42d181a00e4201c81450f240c14141022941a4032900380694100b540719074034112152428000c0e040200600d4000f0041002c1d46007003c0c1c20100624845c42580c03601c01c0030400c84082c0010702c3c1002c10b03011b00f42000c0710b0010402d840180d11340b0304400303501440f6201000080184540c001400030200320240c804040e005002c0288454110000c3d20b14040140b020540034170b003101c600c2c2c500c8000300d200b040d040b0680c0008079031044c842c41d440c41701040d038589440c0202c8003640612584039504032521071901c1000392f406420403501d00c00250940c01d01062032126511008150a043c0091b0300403544140d035250003040d40c51074040880e5002d040101b0000803524003a030540103020fa881009007042d551071602d10701e45150300071010342140b28402d014400742390206280c0381403842581d0150192604040451022500680c06041c0c09854050100f103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 395933309 1250 395932059 395932073
    0x705070303141e160519170a080114030a0f240b130c0908030d090204060506160609030519030902040614010203070b060f1503040506070801150503061813050613 71
    0x218100e04000680e4441400c1954201c01c00e2509000509070700c00c1e0f69020b21904400b200504083d440380110700d441d01c047d0901d02c41180514403040000c00c00000c018011142404c1d010100b00b000502124909011a10340081041c2e50b5507080e50b181d4000c801062035104441041c01090540c0700b014003002d8503807004208c00f50250b1025001d07480d034400c90b0030000c61007200004020054001220340300c48022900000511807c02e0891040f4a0054002214103203001664008200380d040c2103040f580584485001d08041075088041002c00c008044400c2e80d0703400b4001003c40b05680000701850903206220131100950408840b00304854940c1c50f0316a800000c41b01801e6211006607010f48901c0e000c01c440a1081c240b4030751040d010741c103c8046c0d1043d00040c40c031a5002d417013294842d444010050381d51080c01e0040800880601500c02101da001d9001150045409080c01c10f111b0702c00a0440040c16013078a10f51400300200f604030f805c2c003800700105070f080441e40303260407144142a62061 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 395934559 1250 395933309 395933347
    0xc1407050a030b0601090e1e0a05060d0212030c010c0e10020c101d0a0801050f0f1308031306050a0204090e0c030709180c080c10020319180506070507030314 69
    0x514000f400c000040d540e0340b103107800030010f009801602d0890304001c082181028041c1400c503c41314500000201208001c0c094103000799009030410014041c40e40900a0301c03e203030400b4464078441085150b8000c0e00c01d1040c00700c4148280d88030241040c45804000800640d19801021544003501c9842d65503141e813840d6400d9091410000c00e04189041d410611340c4104d14200e0340100246030000d100c08040d0009803040d19801c00346003c95403494003c000a040c151a41c004102190201e040080d1815008580001011911a9180e02656624401d45008588041049402090801440205000d08507210050001401030740900101284c0d81b02c0c6244946d500854883e0101d8401c400340031200c0d9072803500803c071410000c4c5c039418041e0382c0d410782d4800b0501820070001060703260344c4040107844220402d0840c0140b1216141d00454030000c00801c10350440310180b00c00a52a44d4400090001c10b108102800509203541009007a9100c0070750400708118080010301c801071518040c070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 395935809 1250 395934559 395934563
    0x301150e100e1905060c0a030201060e0f0a050403120203070f09150c0609020f03100c0f0c081902070f031a0a0204051804050c040c200d140f0d0c0c1407050a03 70
    0x201c25240c3d4160318041c0c1078110b5215580041c0300103000541c44001040151000703010b0b030002c0c000b8542d04c0309034001350705041720485859030b40f05d40454840c04881d0001a085802460001c40040c02d00340040100e0f40b042d202000418200c1c03c10283d820f82164002d802030241041c6280e0f00345c2700340c0b0050503a86030510000e0107039590741c030241c045545206940d12a020003804843c151171b0750840c004001c084079416200803554442e4000b10117441804200d240584c408101070414194a0740c00c15400f0345850b200b030a41c001c0c07070300129402c0c0801c1110802180110405640b030f03146542d44001100c405032800300031600401046c042616007540004110b10701c034110f4511941c4500340039080ad426011815071043c02c00c007100070b11a80c8145e41c204d040654556190614550b0781c040b41d0b550042d80c0d1750402003101624003a507501035950107009403203100c0111341d2500b00c10700041412100120109404981800641c10603c0500d01041c0c080644003401045014240000500010018400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 395937059 1250 395935809 395935819
    0x180a08030d0c2f101e0608030304030c0210020a050609010204030c050a03020d1b050919050609041509030c0f141e120a0c0b0403030f111603140f0301150e100e 70
    0x8071141c90404100318518002c84d40c1c001c0001a201c081790004a00280c1c4000d8615420f005021078a40d4011085900656141d1500481241c0c15402d0001c083c140540844c254000c03e5841c6010460503c85d80e40f09490300c20005a559041d40340c18070604d20250030482c0192442c0c001403006845031001c1c9021f00d8ac02000340d8040c107402d9144490b400b5540c1c4c112a80081c042001c0c0440d1078031a00c61440600e5941006100b6551054144010040d0844004c2c103c2d501020041201d101e41e584020b6100f40a840c000c991540d05480e00581030000c0082201c281c403a0f52540810444184081c078031400303513002d500101112451285945141d00403060b24807480c0060303000c0c1440d010328402006154082406600351a0034140030b4003c01c150701c070860859040c50401c4a40c800e880301150150600503140d00c4070361070980c4080381e00300e464085066401c0001c1002c0f00c040210240590300a0100c0358140c81280d4661100402c2d00150f075141078010a5001020f82900b5045800b00740c0c00981655 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 395938309 1250 395937059 395937137
    0x4713081903180f03060603021002210a030e1203060301061203090e18150901051003020603130f051b01090b0406051e0d020c0601031b0f0902180a08030d0c 68
    0x30380304000600c1c540c050200f400c01c000300001005802e400c4002241e0084449003142031b281107060362115140d10b20a0100f04040840c0c05401030854098491b5500c24039000906240c009240b03403501500140c2e07409606001700170051145000d005860103446c8a1104009420007554007500091482c00340a6900c65110001442d18482800861650700320700c2c101d6006284804840424010540c0d00301c0300c03075003042c00081078820720486d0355040300d9014200d030f865581c442252042c03054501c80e04440d400100302c0f0380350200d03108002800a0807414000039541c01c8404002500c007003941d03440525410701c10b210030403030a07401c081502d80f0300710501c61044020311030f419140514866145041c401610100c0c05240c2a54005403c9042e24490340d1801c20140d09803042126420852182c0e92804150b04070600c8140c2c5190090402e6648c040349083c020101100003c2c0c1d0f2a01c01e4001101607840420f00701c140300d0301070080710340c15441410070f101c0440000c3c1c20490042c00520314034641402101d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 395939559 1250 395938309 395938337
    0x30314010503030f030a0c031812020c0105030106021b040b0603041a250c0f0b0c04181812030605100e01020d111b0d05011803184713081903 62
    0x5005011402046040355040c20781a141c1030701c001c1c400c505444013304ca200d504407115402a0f08403410f862280d002490209a0035005018400f202c035160780c2c229490f9103152185440f0310001d140102d00c164030a0307400c401424950407207031000411021701071f41d0003180b60245501d2041941d001000602d0241c0e440400c905010140804004d401441c0e00d51071010445103411120161050b40d1511510008492600040c0030030b80303a0b10010f10f04005002d20304440041c1450100d4824502da90a000c03540135540c600242c11070b07034007112140c0030803414010f41020b07680c188120a100c425030309107403080021411803e55240c0b441181480102e50a204513002030703450040c0841400e41c010002c0c000580740c006614000e441e40c0a0480110b84003914010248090040640c143c9040707008246075244204112500c0400340020803031007611502d203824440c2c0942450f00da085800c0d9010a588080ba0140415602c4507988004155008400d00001e03004031011090b00b003540500e03260800011903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 395940809 1250 395939559 395939561
    0x19150903050f0a03200310060e130e07031a160305040f1106090a0f0f06090608240d06050105120f0c150c0601060c050d05030903030a1104050d030314010503030f030a0c03 75
    0x441900c0c0d0120817920000b00c134908844000303612426428035031064003a03441505441e4000d82240d0aa401810513807015840031070f50b44801d200c11609001ca031401030b52902c0c1e01c1841e405c0f800314941514080c00c104101158015055003c0070154135041000b481c05461380d400521442c14020036070880038602d061660b44030400e480401000070001c0801c250f840c203004214494500c20f1071240300c030518002605a02862a0b03600701c0d100c58403074058507034440341d000300001c0d6501d828540705c80d4251042b8006071112800e0f00000c1744613190014595040504014601c210140c4441c00e660052503141c0d07c040010450b207518010035036902d507038820194841c0e0303200d004540030070040d8450b0900000f0381640c4220444095401941540e800c090030320001c0300c981c84115480c15580c0c2c030800201d000000d031707640f1220500545a40c0d01d8180fa8803940024603110410105900007600c543d042c140b90810700c1c0b1224018031381100110b00d0301b01032080500c1c40e070000500102150b565424502a11802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 395942059 1250 395940809 395940821
    0x20d0308060f120f0d0e0d1b0905041407081c030f0204090e060a150f0e090a060203070f091205151f30050304150e0319150903050f0a03 60
    0xc020a1400c045003003d00542d80d500403601903840ca40f280d41d1103880740500a06403441c0a60700545080f40400854440c071141d90706146440165851950000440c54040c0c0300e40703030080c1c1c03160000c44101c0401201480c5045140d40020350140c0140002603810781d071210701007030401890704000c0b900b00c204d600604024029503000c080300c90b003002c4040f540c542c004540c60b0b20800100c101041061018a0155840082c0c4d000c0c0240b00201e203241805400340280f03540394421428022922209002d40c2e4040c140d800c1921403401007030030541140340d001d03084403c2c1c0c00a0444520344400520060303c41c0c903958481c00c500c40070b28000400100320403620071070100948418a03100309105e030b50f860300840d242040c0c840d080e50f80080f40e088680c0b20f640740c004400c40720541100c021402c3c5410042e8208600c01921350703020600c0001d0fa005141d60714203021000141d06090122120940305090021012114107020100c1a103412001000260404269081410000c09094581c0c0749240c0c1500100b00b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 395943309 1250 395942059 395942089
    0x18071d0a03150c0909020702060702060708070501061418150f0604121a0f07080106050a0e03070f08061012122c030c04020408030f090307180204031a04020d030806 72
    0x801c01c002d40c80a2405500000e0490303005503610b803040c0d80c2d02e44c881e1040b40281d0000035032100c1d0401c8040050314000e4003801c9298000e103002880c1031207642c0da2900b141d80c0e036400b288a010040082c3c10f083d217024000c0d03c850084006200742d092511502003400c680103004018400c0e1150841050140c4851066070003800001c110f2404000043c280180e210040c0ca55000306044a1800214940d4120b81c00324003030140c03903d9013000da90808600340d03010380141d0000c104102d64900180709a03581003202034020803044025070f214a003045009800d05000805114450031400000c024015144000400040d04500301c43c1d00c0c0c024900044a05070440546445071450700401d0f104038001c150801960014100e0071280c0020040c01400203038002d030b1240410f1070300301340100440740b031038080100b00ca0b010050968007019252003200d42c00d942c4d8550201119076004c2000d2081000c0e009149000c12101181d68040d89000d0340020b00346008003c004080003685400314070551030340d0f2201101c00d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 395944559 1250 395943309 395943323
    0xd0f0206030f060f0a0510082e03050d0201020703170703021e09040e0f071a0409140a0e011b0c15050711010506190e0c040b0706020918071d0a03 64
    0x10400407440c54942c0801c0d00c0c040c1c410241c010548900e0700e0503200000071240083c150002d402d44101e000d07240070000600e075111548110000c41050040c0300364841d0301d0310544544e1018242141042880d150507043c507030065a10400003640401d401c00070035410b40886480c400c0043d81d07026030450190041c1f0500c5640000b14008085503802c00801602d404030742a60200b007808005071043e6924030320304c100380c5899000200207200c0c4440b000c07240301c1742c204103216403031505607100c020b4001c817262040c0c6403004d02003201c1400039410031030080d00d0741c244000c402804102c1d940e41000c003911007244110402d20542c1a00340007040000d940d1201d4800c2c00c040104541d1804000180ca92030004080e200075501c0c0200280741440c3c00301490341d046c4103007021010001d09051600200040290000d03035082d10a0000041090004c07004050b183d1080342c002d41c40e00030b01c0081c0503e0f50291800c0a078607026441c10842069070000c0c00300034900c2d00505090509000401040100c2801d40000e0021 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 395945809 1250 395944559 395944561
    0xc1005010e0105090601020d1b020303070b090303040326010504020a20060108070f0806070c020604090501121101030b09190b0607051c050a0e06070c240e04090507050d0f020603 78
    0x5825520107a0704031542941c20004541d903e8004903110003c210003803000c15050b080c0c445040300140d0b4040c4045201600f2030349441c03400e444001044108603007089250780b0010400040543c01241d03507030455039908003180400101ca142614102050207130502441d808190841c0140c8541000101d0440c0a001450300d40c4002c5801c0d61100801d0254a920b8802c103800040c484c05061495000c98811300054546030b1520101100d40c02c00784201a6800074051201003084d8410784030b1f85000f424101890b001d8040b403490040500d0309610341e610f052515011015102d500c80d00f03941a40300070780307800100c02d0081e903080200081008000c440d82108001c0b03100360403c100011a03035196044540880c401514003036048500b0b1007204100e10014020003802460750600c0c201610ba110b11419240d18240c0c2c5545100c051002e0124a040d00a1294561074400030b8000322000b02c1c40340c00f41c4041c80b50341a25110280d440b1000e01c0b0701402a038a40c0c50001c188041d030740100c564158010700966413 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 395947059 1250 395945809 395945819
    0x816080706091406070e0a120f0c06080739080f0a0509040b091603051504020d0207020103150609050f06090306100f0b13030b060d02062101090e0705060c100501 71
    0xd07188083c03c5440041c032400e000f189065004024070b0140b4180205041101c508040e8040403040c07612404841208007160410002500d000c03182003d8080c0c5c1d40c6441c0e2516168000406039100c0768a003c4001840c8000c200010384103141840b090101045e225031780c0f58951074a20360510031805e8920702400003050050a865004c0c000b4454510226002d0200c07000007030400807044810b40b21003e100540000300c8a0a90080d04001e03070003004458941c1e040e5a40c100410140c1e807040403000750181e8006020811982c05105180780b13001900c200030640c0d4100003000e0000401c500a0510600e01c002e1040c4440d510f2408889254101405581150801d007224480d030704070500a40c1d2081c079058002181c180700c940140d9168480107403411005524580320f9a41442c1d010b04950703040303001040b941d8003503200c240040141d0650090421802505901a9110884107802c00c5c007015042004c0b004945200042200540d08100e80aa0381d4405c0c42803440e142c08010410020418242400010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 395948309 1250 395947059 395947073
    0x30809060c071809060f05010f12030c1a16020115180b0a1214120d02030a0902030610060f020c0303090f030709061e08150a0c090306020c010e011107081608070609 72
    0x2403114450381090006c10740c80c04010b01610806d009440400351001e00810540055016040d0f0b0303d402414a8504450700b5200d07509a0781c001000780a9010b1410207004080a06658051041d8423910081100840980424550840c0743c132800896040c0c0c3e84c40c0d004501e00c0e1381d1104034107003002002840740c981c0e44c0d4900016142c10780380944865050342240c1c50001ca01140351003a07801102800383ca454810088a4000d4201a00384504903030b8642d140e1005031404c00c240d6005814a0b01c3d04808a4907180b4002c1010125600d458119040402400e0945e03d00009444070960122105c0303100c92408401301c2c0c40c00b201c640c40841103d061640c00a400c07046141c0400515484044081581d612001c1140d5100c0d42c0010649020031002d0000305c240d0015070189651200c0c03442c0c001c0d800d076a00c0d1145c07401d80c3c00460140c1c07090703555203000d000c204e40b00344541400e1a200c80c41442c02e20f8032a4445480e14001c410070f0402c0c1c2c48003008194100b007068401c48100301d03441041084820b200381000c0c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 395949559 1250 395948309 395948321
    0xc060f0513080c120d081f0510080612010c090909061e0b0108070c030509220e1507080903030a020d0b0a0915050406270e01051e10030809060c0718 65
    0x580154685200030081c1310780810059450300c0c007034640020720340b00c1c0802c500841c15603222210a2038009500402c89540f0400c5074400140c3da5a10b00301b003414010208054495003d04962060f890100c0840d074554002d42204200d50000380d0010301075601c0d090900181a290701905210004501c90504401840e840440c13050821ba031080802c0d035580c0000d58803101c0c0b400000d00400d80c14030034040c0e030f8039088244400300c1e01141021804000401030303050980740341d80d442d00002c0e004800080b0392061108220f680c8901c0078902200701c0d00701104140d807a4030015000a5441d900081c0800c1c040d40b55401046205001410a40e181595100c2e0324004014550b59424554900007000446190500920060320703507c0c10181c0280100c140d500b01c001090940420303010f41c032540300c013004803800e01c03800740b140c0d85410309600319008980d80c0b007510780d00041a0703102c034540d10001800410050b42c181c0e200300d8010340d07849a549881c41401c4e07160400c158081e05280349000501d40040324250404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 395950809 1250 395949559 395949583
    0x91e05100c05040f1e0306020f09180106050a18050303070f050f1606030b1903060b0a06050315040b0609030d0315060504180519050109270c060f051308 67
    0x10420007000303103030441d0740c1e102c1c41c400e01d482018a04000d02282100100010305910501d010006460b40d96031210b040c1d82000f81185201107000c031701c0c681c0a00348401110803000300410031040c90f40c10060050818010f0b022401d0402000041c0000007806c80683c40c00548402000c481d221551071422038044250107108403840d002c1c0d401b002c14000700000310714484410780314410010500380300c0110010b0210003450b40e40310408030250a40001101c1e00ca0000d14040e2602040c40c00d81801448100745643d07100004000f420010001c990380120100e160408045501181e52650701c00050100e010b10404913034103000c2d0003d02d910458140c1d22080c901760401444100721942d4080a94040c01144540c003109114030186806008403540017543c045455450002d0b1040344840354011690300360070900b1001d6960929540507d0240b9004401c18101c0c2e030309000304201c1ba503c2d4480d480052040c0c00c24401c402c8101618580101d0648034041c941c64580422a82c0c1c07214400d1b914003041800b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 395952059 1250 395950809 395950811
    0xa1107030b0a0b18090c01080a110403050a0614070503060607061b02070f0501050702180a0204080a0b060102070f050607030809010e2e0c0801061419050d0b060418091e0510 76
    0x84e0103100415802c0e01d1051509801401845c40841c00543c1c07040e50003030058495942d6421014004026000540051401030004001c0b480703c0d458100101ca1001c2c50451b40d07211402e04100360039a00c90100d9501400695071182c0703a00cc503140100c040c180c401043c850010318842c171000c16a60020309842161060744901c1e80c080d0352000103641741d100d900806504100c0d00c44401c220600000c1840b0f0b04a20001001031905554000c601d00f4a00d0254003210304035026014049507690400c2090081c2100c0e048001900b40b4040000740d00340300f44c94004040c006c0050008408282c00e600005000d070b050f0040c1c4803c0404646248a5000d070242d01d49615003010050340303806481c600c5808800c0c900e5072903c1184d81d003064015545515800304103d0b84810802030b032030003d03002001c011128a9103449550311078000000d14006c0c0c5a440c032415001e60b500707000c1000015420b1203550b10140414000040c002031908001c1060b6041d010064012214030403424108980010068822500004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 395953309 1250 395952059 395952079
    0x15100e030a020d0308041b0506090d050703080f1803030a051b2523010503060111030f07030806091f0501030b0d08031005030f0a03020d080a20031005010c05030a1107030b0a0b 77
    0x4d0702145c03040c000d001e60740e00700c5403cac400c5044605001028030302403801341d011504000c3d0b07250780d104041e90000d4052070301c01e103000c903c9c0c6403d1400891948095a0100c02440c2030903d03640c802445400307003081c0b604c1d0400c55038010503882c002c00d2044004c05880019840140d01d41511807048900030b03845400c06804080320108070070408010660007012050395606e2441d2035800c011140c08070030058405c0325001c10451506040e00c200000d120a505c43d0b00c0306405e901e031130000c1203030381e44d4020301c241d01c02085149040c0c10340c02c01c04042420b030358003400c00040b01035040011903800440d50b2001000c041001050200e0805034070103004c201c9104400300c440c40c0003800c5007951142c9006500a001d0313849090b110110b140100b003160340c00351130001c0015110400d0001c84150302920b00020090039000018001c00008907405e1901400702801d26003138044103a0780d0607030390b885240d1602e0108030408142e0411090700307010140046070403800c0c0040c01d0601144200041506011161044002c40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 395954559 1250 395953309 395953343
    0x10051c050402061b0712030f170603060403050a120906090512120f0402180f0702121206130905100506010905040b010f0806042003040b15100e030a020d030804 70
    0x40285071240d50301800079810800c4400c080030120103100020013260040c0d010101c1c00322a490b2442d11081d000b940e6400c2181211080031300000e00206061494a100f68100501510300084481e0415410320b03025030340302a4400200d445808120810760090f060100b210f05118494102a40950042d4156681440c990701404883d00c1100e0f0150110322003200020840b61014201c90360050010704400307034214402880301c0051008a50711100011190305210106904015045048148010b8145030014aa01c000c80230000240081c1c0b140c052030110103100da1079508080704a9501204a6104c140c90303503032800282c0000c6500500040c0a4000083c027071829000784004070030107031107116010446050403500f6880080040381c010340c4075101e1280c410105000103100902c6096101e84070b05040c83c0a02c1d18981c054100301514007406c0c0d0105807030f903401c880120500f986060104820440c0004203040880424001c1c1d4840b00e800015814903401150301c80c490743c401e0700c008002014078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 395955809 1250 395954559 395954561
    0xe211b0108010513150306050a0f0509030309150907050604150f0203090603010308160506070302041a030615070f051905010b0d0503091509060408031314090a091110051c 75
    0x1d100f500c2e446000c6240c9035103c44000d5001d009045081d04091800716242c0d1216402c0c4e44040c2c1700d601d02541c0d111010308148009100700343d00038860710061407950a1003081640c0c0d4402d01401300300d80342e82d0304000c500d9207041009108001c0c1009046a52919a070700d2403a140300095074100d2000c5001c1c050b9258000b44080104e50344c0050052042c0e007141d0035500d60b01c02582190f0044208015085260004200100400ea224880701c2e5409a602c90400d68648001240303204883c1140c107003802441940d9403a0130800892940c1700740c2e120b40b0b62550b42004440c00075280c2000e040760240e2900d02100b00e8a1444c9404070030700410080c01110015401c1c08121007042d84054402e070410300c80e14007140f501d5045450094011102c90f41403048080000b40310f82d1080d840f500480e440000c40808165044444800402ca03081410522544807000306400b010000d000840300c070341e07403c5400d0420030452005400064040c045454114003020081c14542c070081c051040c4090320740c0344415030909 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 395957059 1250 395955809 395955811
    0xf0506010b09010c0312020702040f0c030b090c1905070c080601030308130b060405070509040f24080a08030c0d1e0e010e070312110a0303090213060501020d0e211b0108 74
    0x10780d200902c212442d00d04494504662246200f065008c000e1280941d0307980c0240003108180d01c80008200c2c00642020b400c540030421401d000d402c850041101c0b50b0010302c16500d03070310250562001100d60101080b01c0501c84d040000b886944070307420100c4ca25100103140c0b4140c074401d40700d4034201d8441038802090350750101c034010000b40204000a606040c56004150041054205030303040c244c1450001d020389215203407440c0e11960303450040001040d4860240380036230890b00844101400c01904a4807280300c0036001d411004004041000c00c402e41080320b100d070f8401a404c018013201e440000307200300c800d50303848030100e410310700603c03004c0c1018482c00d021480d8100081000303500e982c1d170300503911004840381414011200c624404c3c81000740301041d500c0d4481d0f030300001c19034030520400445150003420603911a2500d08180850f0340c00191040c07003a0254200102d10369076200000354180d46180000b4040030300800c001d141c0c410001600b019401640c2d54031003180420720011558044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 395958309 1250 395957059 395957077
    0x3090303040201030e0313170616081b0412030e090906160e060f040f08010f140f13020307060c0c120201050712051e040311040606120b06090d0f0506010b 68
    0x204001080040d80030b540604401843d45080d6420304d10050300c01013500c0140d80c01401c6000b0140d542d910090301c144040e40c0c0c03041c01d203d0f80d0318450604110007052040c0c002e00224890200c000d0b0b20300801c03030020698005040c880c00000a2099a2400030300000780101414051107030080030078002003000c0340d09840b51440703140581c01d02c0c030182c0046901440c40704071260000c1c1c017000b00200c2c0303051120041019001412440d00c4071131400d950b45084418114861007920f2a2840c85075074500382d0351056401c041a035a21804c5601d44600c41d059501090000030b40c58451450006144c40c2c00c0707400068218050f010203081c0f10b40d205100b064011040600030f00140040008074002250543c0708510114203142041c18610014030051041071400070754489208040b4040081000c4060710300280c000583e800d01c0003524200000d807000d6400000caa05850700c841003008962100010b1320f03200040103024100081650501c00c40402e214034098503180a044008030300681c00d00308868181c9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 395959559 1250 395958309 395958313
    0xf110c19080d1d10060302210c0103020a1b060507091a0f07030c0f3206011404090f0c05040b0306091f0603020d0c060f09030822170a02150309 63
    0x4402c061078540103103c80c400400099101d0003256001c50001c006104070360313540c007200141650a40c01049a1800180c040c4100c03d810040b10078103201011400d060f40c00400e09015840304441d0320151948148902224514100558084117100550704120b0240941c0d440d94800c0c2c07501c8140c00661034070303200816442a4010000c0d07000d9000f012008140c0e040c001d14041c01110860340d10071941c100d0742401510400d141e507401d114182d01c10b100170640c19080030381c0040d400740b12088403a00e13035a0500ca04101c42082c1145002952141d803c140f01c1d0a0303000005c0300d585c200c036280401c04100c040c003e5038041d07031520340900902c2c10002042402100544000c140000c0380303030000444035100010181100c1d40b2013000000580f251613a10740c8040c46043e80601d018140500106540658200041000403070f020030000300b0841422500380101e001800c3d014045000c0c00304000e600c1c10707803204000003800d21510210400202e48036406900c200d0328044003901c00c4072508a1400180c0e08501d0036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 395960809 1250 395959559 395959567
    0x6060901091518143604050325060f05040b150307090f1a010201050c0f030408040f03140c0901380a09051903080a0f030f110c1908 58
    0x901c004056600ea40c1020b454038212620b0454069188468507602400100016820708031152806030105801e45040407003007950f084040c5d03031070140449007510810090050001183c01d0080c24000ca0f00100d0b9191048488140030040c1c1241e0888040320075104185048886228085a4016940502d420410345034180d03c0d4440b0344031138000d00c0020240d051199810014040186004820307400d01c1380200010b24108411070004a29410024681107901d86000c02c180400104241d5002d41000c0b04827548a0303035030f407420304058030581d00200c80b40703550100008104070f10344102d100b0102d0107400b41d031100900d65050000ca828280111030080c1a4040d134654454ac4580101400f0140380605107010080c0615214080c0e02000c1c8480018400d01c205100a051040c09682e01c002c600c0c20013a440d43c610b4036800d04600810100030100b000880d210400c1a120790001080e8640481c030800c0300900252030401c0700e501024241c40e107401411840302881e100400c151100d10b81010035607140c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 395962059 1250 395960809 395960819
    0x1506020c0a090c0e1009030b1504150e1906051207080f030a08060f0d23010b01020304030f080705120406030c09050102010c090902090a030f0f061410050f0f0301150603050606090109 80
    0xb00c5c0d0607181600d41044540003000000c42e0560310241c0c01980e41d214004004140803044c030080c0da600b008101c500c02210081040600d540e07040c046d60014050700051215100e028603000a04100e41c811a4001196000c2c04a42e880203e291001c5812200031034001c8141c0310851509c0b40110703c69540400c100100103540360414031517003400210b000307100f49100c24407503031540741c6081c0b6011070f6034500b403103c099042d40c00000d100c0c00000300710900040d4101440c580d0351644103003c04100911008010232803008100040212307080c2c114000f4080ca445907202e902c010003c0040200c0440000c100020000300b650040c0710705503c212699031034041640c10200d454010f94054040142c12813a01c00c0004003280d650300c0e0304424144500c80c5a0f41e0300465080c10002c1e290580d5015000c6018030041c0901d0311000e10502c011243c05403030301c2690f119a04006201d843d5038079441600341d420414010406901c1d1850141600e0040c0c50400094543d01705110160040d21010340c00714a12500c00c0c40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 395963309 1250 395962059 395962069
    0x10f090303081b03160909090b04080d180311060112021809030405030a030915020106241209061401060509061812010603030f020c060721031506020c0a090c0e 70
    0x250240803c81075030200070006075a4141d0342d000f2100024018500c00515402c0c5610100440040811500030300c104001c54131485e90501e0003030001000ca400000381c210500100c0e800c0b01c0030003421206e0303818001601d4140074003118080c09032480c40b4041c500020036010205503c0111040e0041c2c12842082041088507038508409010717021584018040080c10740d800f04518424144241e82e0903d07524680140008941200040e2100390b90402c030080c400c0300000d01d906141e01110301031070229aa1400c505503145003480400e6440701e4203040060041c040d82c0d82181d03501085002000070560780c2c42004071058025401043d52001007008101022040b21480c0c4400010042403c600c8100700f4007410300711201644220040742201081000e01c3d901440728440801c01528100d1414189aa848044000c28070240841c00c5556071a180035a00c258090008404e18045111043d5103411001e03644079441a0040c3c460b401d4844d000c145040389000b0760090005036210b4464014107041000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 395964559 1250 395963309 395963311
    0x301050609040603020a06050a091502120d14010b2503020c1318061d0d090302040e0316050f010e0a0b0703050c07060c081b090d020f130e07090b010f09030308 70
    0x282d803154550b00c000c00560740c0e61050100410044c0c032969902e08108001a2564607585d00c40d11307552904003003110800c1d40200303270304a420114003010380d91420660000002860011070142103c0e06075000070440091500040800c1d02c1c20000c505024552008540165100031000030300507000008201c4183c2861000b40d00945c0300c0610200e0316034078a03201c032120350bd4000800e03203403691942d04810202060b0b280300f011582112000d03044582c4031107001340041009100090141b9601d01441c5582070050081d035800c49807031000c0c40709002d01820203d64030310902e00c0034420b07940380600700911040005280c042299019070b4540c0e171941c5018050700148001400d60040f80820056100082c0d420f2181d00d8072140705440e41c0c14141040c1100b2207400101c49240101e0381d00c04c0120160715503940320410b809603411541d6403001010500815030404400d80c0b40e00a541c10022030b0420340d44041071090a0b035441c00300400060100d04e004584160b1000300003004610a8502440800e10420341a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 395965809 1250 395964559 395964577
    0xc010809070902030c0a08100602030a0503100e0a0b13090c0302040c0c02190608070903330908070b100f060f1701080d0e041b0804170316030f1103010506 68
    0xa01c0545540c0d900e560700b030740d104443c0000110740002e940c1845540040c07859800c21490000342d00c4031410200d01039960301c54640ca01040c800044009455040401c1664001d060000c440c003001d0308080d20503c000d48a0003400e2032142c1040040c2a42c015114070500c8804c580109103040d8403482e680901c4001d20541400324104601d507c82003001d81c40d0440c20b40981c451a4080c0ba400f1450000c0080508030064039403010040a140100089245206401480140d800c0c9000d280242601140a942d0040c0168412039080c24040400d1001520103030603028012041c00e5916030f0ba281c802d00c19035000c0d0148a0300513404080031310106120310000b2070564141c0c2407582c40c00840c04c804d2112100243e2041c1c0c1240d2040c00d031000520780c85050100b10300703000c0c0d4003440802100102e2540d02c2e00c0e80545901007100300800501449808510400c01e481c0903d41c4550740e041241040c1003000141000d00042810400c056007400c9191080a04a5644002c1241507900b0901003003202e070b10003000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 395967059 1250 395965809 395965813
    0xb010e0103110f07150605040c08041407180c080619060804050705090a1a090601050a031806090302250e0411130c02060603010e0f06040b07090801060e0601090e07020c010809 77
    0xd0300203080c3c4064010b000860140303003051120542c51280e4002c0d42d1060300301b40c0c05142802114414a5007100f40b80f50030550200100c624a041111501c0c03800c0920350105540f06005945c1c08000001c03a13019013914517840ea205001c658404d028410308902800c1500000140500308006480c414421036402c188202e007900c1040342e03294001849007505030343d800c5189540d80141c1422807101c1c00c0c00340754464290361483c02c07868110006016805816111030501d07442c2c0f500b070031254040c0120b107002c07240c1c442d00c10001a000350400a5860110a081100c600c103613001d50b4150004800c141c8040326481c1030480340660303850ba101c201c505001d0320b545820514400e02440043c600d03000e0085054096802000c083c80c08008050030342d4038505451450790000c6041000c03803807000c620070f54000d13049892841143c0780e10000700d4102c0e015074440c4555520305240850003100c407000050040d04240d0b40c0740680b41d01c0d0840c00000c600c0998002c0d01503809048441a5075000c0e011440d4800c1f00300003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 395968309 1250 395967059 395967067
    0x1f090e1923011401060201200d11070b06120a080403060209060c03280513050904170c01050103030e0a0e063102041d01061205220b0402090a0b010e010311 68
    0x10300e0340304140388103030300700d080d0b510b4010700d41c01030020019060052025100a02112805408114a400c4e059a880c00541c100003500e08040320160402803466080420280d40c403802e0f0705101d203424406517111440354401d5081100e07215000550764002a030001543c0b4905840c55858100030b500036200c503900710009104510040c6e4003031015200d440340d000c50003460322001c1143c000c10042c0c0744145206000301803240f10307965800035000c24140c810980300d980382522203041c006910302203804950085040001d0003050b940b81900001e04a1b23200e80c030703000c01010b619010040e4000c1d087c024004000c41e20800515a4a00300c2100c0302d100b0701d1000c10304814461078144420b20400b012640b12a0f5030001030801c140340302424800c0203021a0202e4202a50500000400f14903d001c01000829100d0002c01c012102d055103003211714982d1906100000d556141c044030900742210240c0c4624200c00000b01d40c42c0a601030405201016986c900d400c40e1544019001408880d0190380d4410f0140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 395969559 1250 395968309 395968343
    0x2526121b121003020909030c0d1805240c07060e061602011d030f0d080c070305090d17040f060e0a03030f110708060a0204081207020a030201140903061f090e19 70
    0x3440f6170303004041a901455403586840041e078500800030f000b54082100752040c0c0c0030902c100d10218419900201d8005562600d0307801c890f400c80050008202c40c1000004012018001c0000e0310401c43e26603031603004c4511100d20410901d17018446400804c41c3c0040d1840d001980708400810401c405180c1c140711869940700440c2ca03054600007252044d610400c041050a90054060307580074145441079072600e10680e030010517a0040a01190040a2410311217003040403c20101041c640968100c684403503403104400440582e030301c58180442c1d142c2c00e04400b07600f44210080c0580f501511a8144900c0d0140200c03001424841c0c40c01c0c0747d005004001c075030341e5818407105004000008016031503d00f0141d03554105152000ca9140780201008004c00585402d80b0400c00c494090034020641c00710a40f1101191250062456050140c01708000030600c400009400d401c084260620300141c413007020b0340440b4004002510140d12508000a0084040002d001458820868040d07600f03604 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 395970809 1250 395969559 395969569
    0x15020a060e070617060d060b03030f0f03010317090907080612030301030605060a0e040506010b070305220905060f2206030507081f022526121b12100302 67
    0xc40504a80d07030400a07081089940c40300c0c2441803044100070241c100d01700794000aa0400340ca0300000c1a00391510b011500715607061094810718504050450b54802c91310040140940c0240422505500490355900a2007502025034805070300c09003488000792120a002d0758120001420142d02c100001401d9540d10301c00c0c80610f000314880c100c04500303400c02d07904120714140690040000e06441c0000c00c004500001a524115494031300116030b02e03041c600741140ea07846a4a80100300720202100507a206001030340001c1160507c0300100400e8442404012600c0a0504803a0f4002c0c0b012007442c40120003a4a0305000305200380c000110a80c3d2a9109820140544d010043e60b80240302c0485081d941d0080003442c003c0450405c520b400c000341d115a001c03410451540c849412010241e40400c0100d80354808003010305c0d010f50035241d035408010754081e0f110171007070004c88091002203042e103050101043c0c0c1c070b101c104150500780700c9401260800c08500504501c0050000c200000150300d031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 395972059 1250 395970809 395970821
    0xa06051c020a0b0c070918120816031107060209060d09230703030f08040212060c21010f0b0721080a1b0818070801062603031015020a06 60
    0xe800e11200105040c0c1c010401d510b0103640c880b042c0280200110700300850003090403000d0b103e01030000a0a9003840807540b0340c10f2110718008003242c0452080008058008124030f21514080021041c0c20721402030450643e20361f240800e4042c80103114050016841d40c001c0e2400000c058500c606007400102944c3c19140400300540b14415504c803040355484d2030420307141f104545c2000809217180f5559000305107040c615454010058400c021070119a40c81e07042ca03510618a030704540c081d0601c05106500c641c407211103400c681c18407500700040c64080358240c504a801040700c0355981440e05003a0442d0740d01c079500880d107a548501d003001000c203005024023034501c159540c1550038a048013200007140c3d106803202d40c8040c1042800c141032640004a41d9000d40d5115105d41650074504030a40f0745002c43e00480f038030303500b880800300d001a000b40c020400c20040b40080700b81d41504070207080e00c034442900c0071207000104040601043d400000904501c5070684100e42d0000401c0d22100205c880d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 395973309 1250 395972059 395972089
    0x106050a2a0b070804080d0203150d0302071d040c091d030a12050f270102040e1f0b030c03070c150f050f01150c0b0709050907020a032a0201080a0605 66
    0xc212015105000880b4000340d8005100d050201c0981065201c400c814011843d00e00071060300000092285600c15600d502002405404220b40f40318518003e500d6000b070303004101d01344012b20b0b0000444d43e05408210f0207950400e02ca0708429042c07424032805041e8a484d40080c49113616154602c1070b034101b00070b10802817903550b007601141000c04c0c000b081d50070142ca61144113402e10188917640d80e2035500d54030701c0316044901d681417002d603040c1c031400b84c0220b80c400304646150908001d0200742040329079140c0740342d11003400200380c1c60b00c000c012240425102c504c00f2100a00010305410b028104902030540903000102d000e0f0164007a0609580740c000341c562140d602d80060080001ca150380311707805814051a08a94030210800c01080788202035009003410112a000c21011806820440d01030b12007c1c00d00e1000b032800480107903840045c1c0c01c1c110b000410040001011300c1540700c41c000b071000c2c0c0080807450308166400440b001c8070080c01d0564074a980f000c00084558881c40d50f078078189 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 395974559 1250 395973309 395973377
    0x209060a0f030b01080106050105040b0a0815030d1d0603070f0c05010f02040b0c0d23090d0821010e010303080a02030a0608010608071806061e030207021e12150106050a 74
    0x4d03050900c05401c1d550154465818000240010b004842d02001034418140d01440e201d1b29540c1e506900740d520000c2e0458480e010b0040301d080804580c0e200c1e180c00c2e030490301003503104041c0100030103006c0988400c490002c00201c501094810312845000b1603140d442c05070001041c0d01c08075a260000720707401640701d80300c0d14400003009980c24800b4049412309030f9660a0980411880c1c1c40030001003001d0f90488000d2030000144501d05035030350080704120310303001200b03036440c1c0400c403031159114802101800101040350340000703800d480710010281a65410740e584002c5445042c02074000e034201030903440513980ca81c0404a0040c02c2403040030001c2c00104024100030f4648104048803a081040340c80210f41454000e002d5035401044182d40050060012098082d9000c005c900a0040c41c0d0002d602c004144500c074038a4804243c51100c3c1d660443e4a00580718555450303039641c180b0380d04030325481155140104405c0e4000d00c06400218000d0804018038040040c0c84051808401d9001d4094 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 395975809 1250 395974559 395974561
    0x140307051c0204020a2601080d030e03040e01030f03110601081b06071a01051011061f090207111c02010c0b0702070e0906010f06020604030c12053915040209060a0f030b 74
    0x3042ca1000c190710346d007608504040c00c1d54180340c01103440700e00307809480e03041c15118019101907600400881e0028450700e046101c03075503101c3c54942d184661030352041c0c1c0001e14140c01c0b081e00c1d5102062050480383c0e444018600d84801c054119150000c815505901072428068034010030b05442440585080000c19a122507041500300100240040b0113102088550b90344030540d0100090f452360051010b00c8014209a40c0a9035031000c00c0183e0030079140c80c1c1c000b0034031034200103140020041101c8e00b00c881e104225001541c110b0014511035000c1c1c00a90300d05030346004505c092003900cbc0c101d680c1e441519607040d114580108500020f82d040c240e1588030100412145001c504d0400207080d90b031014250700c6c20140c500500040c644280540300b4590030180f005264007440c100c441c04010b440b4202071110200040f03c004140040801d4600801e8042c8100c8030000420042c0030081078156000d0316031100c1c0c0034030603014401011650085100c007004141c60621302004401180318100001032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 395977059 1250 395975809 395975837
    0x1f03051b0a030f0c020a052d100f0605040c0806130b032a04110a11030d0e0f010e06190207080d0509030403031b030c1b0302100c0507140307051c0204020a 68
    0x4444c84076106804540001380d5200019401080b82d00740c11a104407011401c0c45007000c401c8000351005414056841203c0000c020315105811000b03074000220b5040058594038014801602d40c40c0c40310400040e5a000081c02134070f80454064a8407010700d1001a80e41c007117030701180c0b0f05540301100100c1207c10f070742d02000d03001401181c1c0c042590300742c40610400f0701d090381d480580c1c040d4000718400d0110500e00c40c03082c040c0400a0311034a41541c2c0c0c0074080384010714225515407902c0c22800c2003c1d42070003035040c001000000d65500170000d100029140c0c500c9a00c0e0100250090702040740c0410707007000005106800c0d0300130503014483c56030245603203901e1407501818504011075255940c01c2141811004030760030204408040340c01c008020a0319009400d050184409a04001d60040b42d100c1d482031100c1e400442101d0051141d82240c08107034640e8504840483c4c015141035059001c10011b01550408040c07580841150025600c0610103980c000b070f050360440c1c6d0103880018044140d1680f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 395978309 1250 395977059 395977061
    0xa0618060506040b10050708092106090f0c01140c0d1106100308030705070f02090903030115090506040b0a050418021206010c0c05040506060f1b07051f03051b0a030f 73
    0x10b0000000ca074104200c0c00d004002c00c02414054a01e801400030110b8480d0038408244112505004001c100140800d000c0841b480a03e6480c880c5175400c1c1300f0031000031810200000d45151402c00300005208840e100c1004541d009014038041d20320700000d00c580044000c08108500449229403110710342020b0003d1a54034003140100f036128046442801000820b003c00c0c00c4075003000340b9182c215a6030007541451024078501400003500862908100080d04a01202030b5041c0c50340040c7c80341f5078228050307003150240c003240a202d0744481c08110401899489100901c090002c0c1c4c24600c0c1403a0355a010b20104100d02c80d00410015000548510030708103d1524903400402400d12001903882034451042280b080e0148a004982c0c81e404a98141d48903010b81d00b6010000300441d0f035444144184607981090511a030071648a4814042000c1c40c4c0180c100c869148401c90711001c800c03642d0707001ca01408024018886008148400c3c682c440d500c0d10080482015640f008128040c0f046030100c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 395979559 1250 395978309 395978311
    0x60a020c0d1d010309020a03051009050c010201060b030610030e0a03030903182106020c0d020709060b0901020312060103020403060906020c1e0a0311010b040c0906080c120106110a06180605 83
    0x400300a40c4a06070030b00100005228003480c01e00707190000d046090703403003c01c4100c25242c00191040c410f40287c0c0100120036003100107030318400d8040c1c4140c0c2c405100160709881d200e000e1100054001e000181c0d15041c055000841812603190120f2a200710140043c245008410150002521441c18405040d0804048203003100910386070b180380c1e407508860007491000540d450070310000e9080c08006001094040c0c4e0400359820041c1c40008854100184da03410403846580405410010000707184034032242902c05511040c1c002d18a44859503400118102e030042c4090f05065003403002001003202c80c45002e1600384140b1006a40d85055129070b8904406000401912070b2a0546c60b0044040030501003002541810000001d10f14080b5060151192480d001d41051401c07211103c11a80462010102d071541c7c0c480003003039260031030310f0341d4984201d1a20425425074903004203ca50320a4141b610183d01d403a0544c1c00c0703481259076034415207445c440030b074688840403010b42090050b0b5205075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 395980809 1250 395979559 395979583
    0x170c091003061a060d0e07080d03020d050901050c0f070f080d091407062a060e0102300105010c0f0203010c02060a0b03010216020f150408010507030c03051003081b060a020c 76
    0x103c80325030466400901184120384110341c0590700e4940c081c04103202004000c000d17001c80002e07601d481da100c8000500039004546038000203401c02000c1124042c042c0b0406020302600d80c05185441c038202c5e06004c00d80d0100c0703c116007010041042030041070024019100c909204d1a000c2180700c0a03060584510481c846009852340044504201076a04410040c04550000c17602e0381c0983e131210380b080130380c480000c03020b007a041c10300f8543d68416806500801141d260501003060000420209a080390401c004c441820400680140003541c05103102d03034900c44c0710740c110707010094103540407074290ac03000a903403005a80208103125210545018404201c401a4001c600303200d070500b880195001034200c0680180c034014400c080075110a1001e02d410f902001c03c0540d11030343e9040d05030091038121131103c0028544121225414440c0c0913450081501e11032035103001381192269400b030380c030506e000d4580c00c1070001c00440d58101800018802c0b461442e00584540e00c07418418101500d66440d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 395982059 1250 395980809 395980841
    0xe070807080610020c042f09031507090e0402121501060f050f03010b2203211409010806030102090d060e0706050415030b030307140d09051009170c09100306 69
    0x1ca591440d600180080082c05c0844001c5010801d99000c1a10b084400380041c030012064548181c00600e0880100010070041c2c0445d98102144030b510740c85c7e40000e984941c00203030828000c100c03000381a6810354000d40024208001e802513004264074068400d0441e10740301801100412a054005500003038040c2c850514070718210740105000124441401000b5183c06d02050400e004c1e408a10001c0c101008400401003a036280c0c00e24024a4240a1500000001203001c24000e280f060180141d115030743c061103810040d0440064926000c010030451f010343d4240300c20b0400d80d456108889849014100020325901d486540703604085680e00310f901840800c102c2044400782d40001c41c0d001d00c85520700000c0060740800002c0c00d41c400c402d4080d0030020407140c0000b4a140c04030341640746d400c2d6511a403196950707070310500a8903400210b00e0800b092000d1000c1084200c10685041d480390080c0548040140590008890502c2580d0003496880e0b0405c1c02e2041140c00e10440080d400c0c0000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 395983309 1250 395982059 395982079
    0x601050a03090f12050711040b1806030a1704030204140402030304030b07050903030a091532090d0b07140322150501090203060a050d110d020a0e0708070806 69
    0x181980c410030100c0000c05507503080c444184440c10009403146540311043c0e030101980c044000b0903541040e4000d5400c80b448000c0b03140c0c40c3c81e0502c20b8a510140242001c0c41d01145d0003d407022043c3c0080c11143c041c00b070020000002031901ea03d44805510b0f240034140c80742d04500501080341c08001c5448660900f21043c0b03c05a070300003083d1001c581d8801e00c07000841d13035078280840d03d038040c40c090706405100118840c1c440a07001609202900d0f802c10b0282800183e140382110710174180488213003001c461400e81203080e110001d00c001c205004042c110315004050700480c13800c4060540540300041580188100541d00560685a42903070a003920309504010403494a880f614030700400c080840c041c0d030481086500b02d05190b00402480c4100043c3d80d50340101e0000c0c0d4001c40d0924420202014045500e14000b904184829040301c2400c5005d00c3c1c1405102108103c8081668401a01c640000e030304403172030b0352983c0301700c0803950f50b5522414500009011141c0c080c080b11722520440d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 395984559 1250 395983309 395983321
    0xc030118080702060f03091005251103090d05030a0201140405060705070201033c150b0f0405030d0923010816121103010f0605030f19020409060e1608 66
    0x55810140c0c40e007100032076a54203018800212948104d04e0000055140031082150380003000c034141000c0010443d01340f203583e803400c3e203a100a400c0302000e0305903100c000e1801c0b588944201341448524000c0303802c07030b4a400381240000d00d02040343c0e10119001d500010300c0c082019428020324401c550340d9040d200321400c007565455200c0c2c20041a00c010440c0110722a0705681c400e0b08109202b008003070702c049a200c00c140380d1000d950f0f081c02c4081620020303140030300c00d070012520801784030408000f5a000041d05000c3d031600258403958182140450502020800e9542400310100145450716a40d0150386410340c8141745900400c0c4400703008010340c10088460340c010230b542ea07124145c901008802c40d1040130554100d1842140400840d160584550507070410000a505a51500d112201d000307503140002c60b010b100071540342040c0301100002c900d0340640c12203010201414110054149030300e07100b00720101ea100e684a4804020180140103036403060001d007500803035541c40c082c01c144c0313011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 395985809 1250 395984559 395984591
    0x20303040e0a140a020901090b0a1d0315070f0320031915060507020f120a08160b0c180306040302070612110304050109030908070509010b0c031b010606020c0301 71
    0x901c10074102030425400680d0000d0a03500100350140e10b00441c80a600f0815003400c02500001c3c0c0c8240460500300020440c58110410365070181c06554428404884810510040d1520014ac0c00c1d0903100301d1070406414030750901c0091161219640f103111160705100000d0030395107550503032180001500c4c1704070207510210007200c0d4000c03203940c3d100050580c840010001030071100c4104031710080490010440503849001480c07540d0084880091280c00311f03042005244114030124040d0303000c000704e480080c0d03821001d440d0743e04136078454213640e0205440382000544200c410b0780002c100001e070b1002a582c50706440204401c103400900700307840c0c1039a0195031100d0720300031141030100c482448a940000c40d00000e034076140401c070f0141c03242841c1c075165000e04070010044001c10f4040e140480c2410b0006010001c8803001091900640d1a040c118580f50b80820440c80c81800104280b43c407203403c1007040088512518000100303a890510003d041c61040490184283d0420844008100b10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 395987059 1250 395985809 395985817
    0xa080325080f0708071b0c0f060e03030d0914010c080f0708040507061101110d09140609071e0503011805071d1b0c061003050601051f0e01090f0902071e020303 70
    0x62400c0c810034039201d443e8140d840c0c0701b0441c080718004010f82c2c000410810040c42e818101c4448000004082e40c80e00d2081d10301d0210006466055801070090403421685030f00100d81c054010846404010101b216070b60948602e4940315012800c2c000500c0090810600c10741d52140041c9025942820607541d450340760f030840e1003150200482101400a071035003c1d440b89162208401005035184810340d4041d015240710003090764a0843d0406800b408007010a0061194000c0800361138420f0030a070704038180804640240c210304130803e1010a6640b02413040c4d1151008046802c080125185805031525099070405403020341c82e1003010500c4199501025001000c0f00c20102c000b81d040c09145469004030001450688280403c0c8405d801c0424030f00001d90780a9070580d105a0307260000d001c1e14959075100c0010032507110b105180864800c02280ea46000705140c01c0400fa1b0381d444d04140c003400c0070b406c4480000e50000d2400d041104603c0e0710b0b10084001a10004500100e400280c2c980c02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 395988309 1250 395987059 395987071
    0x506011e120c0203160302010e0706111906020904060b12061e06090415060f020d030b0a030320070603020c2a15040806040f02040e01060f0510020a080325080f 70
    0x103110b08000304254000c0c01038071509500c3e80301484142d40c0505000780070b011001210300540c040c50700c010400034401c26103140201300071401001004a0f101d50340c918190082d106846443e424024001d269413036005200080c01c4110495444d1800a10718840364900a81000d10451010030800689050340c00d4015a80348100c80d400c0d01d4000c541d000c100135140c011200c0341e0004990f01c0108600d80c001f288161514400d900701c0c0c080e0021090150205e84010201d15813240c1402e1007080000e2003900c03080385440301c0c208041d00084011102914080d85600442c0100390003048030403048200300440400101c0c2c94000803c62040c9081d504513441800503414041c0700140990030302074901303004640003071440e44100c507618901400c1590044ea000c1d081280f10300d06120801d5100c0c1014000d08081e900d003000e601e6803036803401c0100481465525100c40550046802800105440301c01031403051200e07a06810180301c0001030ba000800325001140207001608082c4072000300100d5007194001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 395989559 1250 395988309 395988311
    0xc0e0f0f03010e010501090504050d0302040f090902010e100302090f09010521030c07060207050a150e120f03070c17070b090402031e09010905010c0918020d06030212010506011e12 79
    0x240c00e000400d002d0100c2c62440b05040d802c100000442030025400140f1a0380108103403800d43e80301c550111306900c114410b40c6114103002301c3c244a9000c01e5880900c20301d02c141020103001e00010b002c585944a0a880c49004c00d902060b036010504103200b81e15803c820490f0022483d41c10000005c1550110b85605106520014400300012a0410480303c080302d4040c101c81c1c00d6681c5002c02551506c050103854083d5031030003000186801540190084480c440c2c0b9808944140102071049590202d48000700c2c910880f0103080703218600b8001410103d000c0c814580c005170608a000440381000060000706922020040140903403107403d0314004070040300c025945c0d44508546c803515000c0e0500001c4c01d40d218000f4441c450300150b01269045200350000c0c0088012100103076006a1170703208418061660328a145528a459401407401c5c0b9501c940c000349403030f240e40100706520074050b40c01850760740d6102445502e41c1c0050401c00d00e4100ca500032800c855401c3c10042c21b900010030481045 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 395990809 1250 395989559 395989579
    0x2d1115042909030313240206040f06060f12020f0d050316050a1401150503060606160510020c1609020906070b130b1005120607080708071103160203010c0e0f 69
    0x15507400300e0390048401011a034454408000d000c24510702c510440c621503960410b00340e0070904007104540140800c1c0c02916017507503681c4a001d06940318560407a05d46075160004241c4040c8948554040d0510080c070b140038000304e20521080b840030020040c460202142080002400001100c5802007000d2000702c1c1160545031180c501120741e14010a603141420b4400340d211015809080100da10724600c901c101c4c3e4910900d0b0719500e055a820b81c02450030005d0128804112680c1514540305d0b0b07045400a1040c0122402240c010010808aa0700050f000703904102940e00c210015001c82001185481d90120000e02d46205086c1c00401c0c03980041c0000e840340d603040e084000e000e83c014403842c0c410724180420a4488103035001701071146180c000300442301c1000042451041401e078071604c5290312850001d072504903004240e107040185000d04034000c0e035000d101038951050106c241d1007480e04244101420b6800c485020000c2000c04c8244801c0ea81d20980b1040c68030b03105076000002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 395992059 1250 395990809 395990879
    0xb060d0809130209041a010f030e030c0f0d0815060706180f03050c24060105090d0f0305030a060b0306030a11010309080f0c282d111504 60
    0x246005032900c00b9440000c404540d003210086800070600440105d40400c814010040b50806102035501e40c80d00286100c03039085c210034080da015002003602801160b0406140c019014035295021122000e10381003694030310122504200300c1a042640c070340e40300018500d80000304e001801103035000b40510f81c950901d250141c0c452060030240c2508402c0091500d651401c006c1c4c02e90f0300c03840e504401d600c60084c0c1c401905080341d001070814404d141040031207896603401182c0715004510829801041843c2c8603000540c48035010048a01c2900e0310707502c0385442c145610466119901140400501700100300d910f64000c184072211603800790300386490001c0b04004030002c00707041c0310007070425400142800351102d04a015000c8000d0b13040c04c81c1c1000203a20541c45101013102d680111364448803003e540043c035011400341c64640d00c29402d09a400205840d4010103a048000b81c40400c02e1140c1510381e410b011020801c1000082030711380c602490110302207403000c55003010180c81d040c03017800942 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 395993309 1250 395992059 395992073
    0x5181b012d0f0c151e09020109030602090f06031303080106030e0a02040f150915080a0308010902030a0b0612040302071e033f0206011d070f1707200303040b060d 71
    0x1542c80c3c00901130040700b48030b410305200911144501a601002c4920040f984c2e8500c2d00455840b2a4180d403941c00092543c0d039a41c01a4102114143c0c0c00784481b90343c41410f07207482002e184100150042c0002e0718000c1c2c1400361030750406800040801d4103080c0daa14500c840090702c01d640c1503043d5000681c061110f11454024201020341d000d00940e1076000090080c07058000e00344007252151904001d41e510b0040300e9440300c201c00010701054504004010000c0254007645c3d020b4244040410082c241d00006101c40d80111001d1072800100c0044c0001c2c580d04000c0c0070040c0046505803070441c0210929195800300720301c070050440504c620000444a461103504110f2280030720340c60700003555190340c003901825003405280180300d40c20000603400881110100e6000904015442a0310b80c1d40049540c0307490301d504401400414400c030303903240760301d419000d1040403d5a2110242400c42c00701050701150180c5944003a401441440041000c400615030400000c607480580c005a91410b44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 395994559 1250 395993309 395993327
    0x100e03030402011e1205011202210607050703141204150b01081302030c1507030f051305011b140102040f08060405030406031e050a021b0f0c0405181b012d0f 69
    0x14641e801c1c040002038104c6030300040896140300312a03009480d900440c030960742b146000c1d1800c00581c0100d0105082c513019600600b0041c1c00f07840d000301080c00745d1000310015804125881c2e11400394904210a010001c0403207680d80002704000d12810050710b000811044d000f038140400c0603900e0040384115903080000b4015400007920000902c0103403e0500c803103421071402030300484c000306040001c0d903208008807104a801001d4500e415420800111a00c0700c2400180040300c200c040c45501203045125030400c00c424000000d80c3d52400c000c08460311581c2e550008089920010a00c00024000300030341d001c0c1d8049240c00070f02e4480c0001034000d104081d10080c0c0100d840c1806101e041045600101801c040301e09440d030307603000034a41c0c06940d404164502e00d0650094042105545803d40007147c2090900138080003280407540c1a508004c1244111800070040190200c1156004041e00c0c0c4100d007085c0041c0b51440151300c040514080440c5880c04000341007105061181c061980f034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 395995809 1250 395994559 395994587
    0x903090301181407060203040e0a02041e0305070609060507020f0105070b0c09101b03081503190b0a05040506010e040201140c062e120203070314100e03030402011e 72
    0x80c00148160400503a101e4403035071007680c2c10080d040c00e440075450009131900440308036600551a1625014866000e0314000c0e083c4540b1a80804c0001803400813800d0441741050a00c01003c001da1035031901342e1500301320f54007100502180002c1040400c4e0002c0035941c07500c0c0c041e01c2e190407015a08004881510401d140240040c07001003d210341242d1480203031154540c15590740031041c00c91101682c2182d070854540030080c55851000c03001034454501300381c10131009640119449805000a41403206040c401b8112030000d200c20000e210f078000d45250404191003003044981040e440e1551968014011f003150320b85810082011a4031850540da5400040981652205d0343c82800035103c08083d1022031280048500014000380449010100325000c2200491414a84614116120b00c2c041040c1c0c1e00d80940b03040000400e41e24500c140c3c084441001411600b006c0018100c22611950b921600d20740c028400c100c0141d82000400b4500869a0440300a01040b01021281c480d25880e50f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 395997059 1250 395995809 395995811
    0xd06090615030c0609050603150d050303070c0303050105270408040e010b0c010e0610090903020312011e06020c1008041b0e06011b0c03030e01050d0c080a0b010302130302090903090301 81
    0xd04251154000c0c1c14034152445541032860003035a89400710b5942580b405056441041080851078804201b01c440c078042c000a0f0088a00d840d2a48078642160421150400401d00303002041d002c040d45403169030b0140908480f04142c10001a6070540040c064001b64202c840d100c2e030115050221103826640200005a490314881d038584042c074a042c1c0200c201b0088560810004904001020801a10410700e041c040c020846c80d011044000d070048650a40650104200705400074080b0450b081c0030303094401c00c4611142e80c4003c031716003210a03640b0807011900300e480c402d10695100d116200208450345001003560700c1d9820706582c11100340089824202e41030000003035405540c032807544038080c01d8a40304205e4025045400444203107840040403151068000d000003400f80c82241c49001c8185080c5042c20400c0038403a080380c81c030044031030114010030108101c13034540c0d01a404200d082881c042d4280040b921902d42107200c0c5010084c0314199820010300014020816103070134601c0100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 395998309 1250 395997059 395997071
    0x40c0905040f0209090318060d1d060105010e011e0305070e060a0906021b090a0c0203090d0b0103021f0509040f0b0310020d0b0a0b0706051504140f010e06030a020d060906 75
    0x2d0408501d01981008030300440042000078a190303404002d0303504504031140e10318600d0f06800d0400c480c9a00c4264002062035071104200c040d14090319003200d842036036a000381207075414880007510050000100904100341000391084941e40780211102c4451542800b04545d283c5010548000c1050806141c20131030101d40c400d074083d0b202d48200c0032182d0b150255503641c50141d0b00c1200551051650320307001401a80882c10301100c0350300001c40206030748140c1e810941c66000081d80103510800c15181d00c05007100500640c90300c40803001d100c5080c814110154040968094028021415002d1050780d884040e68404482908500034084006007034880094084201200a4012141032080c440c9469144141824400c2d40b282c243c941045020f82440000e541e104007601c1e005120708044884880d42421035107850180844079040b81200028a18080e0000c0300c4441059110008441a01d0180009070b240480e5401f0225010360745050b10070b9040c10000060100d0940081c0f54900d002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 395999559 1250 395998309 395998313
    0x180207020d1505040b0903030c160c0906170d08070c530708031f0906030f0b0a0b09060f060f0c06061003051e06040e0d03020a180f030803040c090504 66
    0x3a10080c4540d114800120094031082c1c00301d980d234001200c0c81441d04000f0410207403010b00e4820140d00e6144031300c0b00c0000c0c40b0b4072804d002c41139803020790050210b4144046408039001080c40081c0807001c4900c2c144020b80740410004100c50038001000e030030303039036007140c55104034856412880d465038095030621061051041a210302c880d0707000d0107550054260143c07699800007541214525500140018156145c455507503001c000400d0394100402101d44000031021903074040c8000442c0207600c00e00c441d9481c0e043c8810306e250700400f0b4151407890290715002950b030348148150000ea041e1505038a000c14180842c800d0701c10044085481c0201140604110000180862140406540d00c0341b400340c404405509641c0291031040c580740600a848580000300c00b56242d00c1840148040f5249070400c988604051300241c1d454000303500010500740e80c0f50416010a142d2a07201c0d5040b0100e450003160441c00212030100500c8404000081001c0c81001e22004018001c880d80030045070030f0134 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 396000809 1250 395999559 395999561
    0x190912020606011d3a03020313050103020c061909020a08061611120a05091c030e0a03110d0819080108010c0e1014210103020f040501180207020d15 65
    0x11a4618009440c184e02030325035061060f1011000e4001900307480004403071900314140340c2e5103240782c04440c0c1007035070007501c03002122002c215500e03000c0d401441d0b03181d4120341803503103424054010a06040c01042489880d03a4006078a603840b00588600304944054070b80c4200103040d100501941c80155400041500400401c0441c0a10303416280490864a0910180d075003490702d00c90070601d600b28004814911202d80000c102039004d5181662404400400041040f0400d0781010810485c1c80c604204164000c4d5020007010421113160041c1c502e10b903182242c081e51030031101d0140c0d8100c07100741d01300004032003a20800300405146041c40200301800406040e000d00c960010342d0b0910f40e420603400d0003410329414125028011500750350042c01c064440003c2d00f050001041001c0060390070114040060101d0300d84803101c5054113514500411040200100201d442585800010412160b404414840380443c0410140c0c50310380f01d0000510241c8074000c0a041c842907840d28014503166 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 396002059 1250 396000809 396000811
    0x21c02030907060201050f01030b04020d0b0103060212010b0f040b071a13061a0a0b1c1b1206140904050102070c0b0316030501060f11010e0316030f030908031909120206 74
    0x9580407102c08941d00d220807800da1300d0955400c00891003a80050002c10902508a648240040d0241c0b0101d00b1640da080c03030212003644103440f03950380400c2603214100141415801020045a60340c103003160482c60b612144a14072480c10b0030a00040c2c43c004000e5900001400c1000d8111120320310710748000c0c003501c101d120900c200c0301e541c98100341094a10300d00007040c100aa0182c00300c007070b00c0d040ca21b056000350b0040c241101c080b640d0300403c3c00114090301409024130703540c210040c152800f644000c0e1402090011000c00c01d402c040e01401014011030304495401c02c21183e10b01d41d40c6441c1802402032003203000203440c9901d5280302140b42080345005501640d9004160f040b903000301041142243c1003030240b2300c001078100d5880d9245c148500d6400a011030b460b000090030803200341c070030b0b442d42d8032010f400661080400e1003041810341066891940d4451418203004070581a541c902041c4001000480c3d684d000d03602443c0300840c44e5020b0b0107138540c0404022101381d0741d01401b944c0ca0790 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 396003309 1250 396002059 396002071
    0x30c1502160b0c24062b20090408090405060117072102030403020606060906130f05010801080304080a02130219031b0e0310050601020c060301030b09010617030a030f021c0203 77
    0x851848011035100c0d40511134810380c0004581c0e06295100c400030085000e808a8010301e01d01c0020081e000c143c3c2c00c51201440003031181c00c0030680c01c1c01500c50429611907150103244140e15180170440071507951002c0700e0300c0e40821240024260b9900d001a104501110621001d003242c0d0401c03c01440e403c008000e200307054050f07c3d124003424400280341644401c0f0780007401a007059010030340c45d0620001411080c0d0004181908201944090340c0c1400c0c25940901c4a441c0c184400300825600117414a02405144d0080c525140c10401201c1e43c0b03110b1000028003540710081d071014482101c1d0b055070145402121102c041c10303440e45c80180603102200c0022000500a120b150f5803d00030f01c0b00150644010b0068500000920520790041c00028803070344c150b01503134000c60f82940d07030003008502079407142840320309a0400745441800c4035041e0300121505283c2022141a1030400001d4643c035014915011a031114030382e600102a00030544150a50245080c40d41000030040d000703148544 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 396004559 1250 396003309 396003313
    0x220e091b0d050307061a0301110910031b050a03140c13240507050f0706020f0c03121b0f06010f0509100f15051c060806060901030c1502160b0c 63
    0x803151001c00c0300011003028018410341c410001342c00002c2458000e040300340030180082c0018102200403a0a6804c0000d00d010102e00c00142e04681d40391540200b1040c0340d00785400c1202d1140c6c2c3c409490707040030304282c0c0fa05100c1c000c588090316078860317001454810260040c8c03544e00c0c00c00003000c00041c3c00110140c5c3c2081d140c0d003000314910030140181e864110914070540c82e4440110b80999241c3e001030000e5425004429030b90b41d9001082001b14010000f0f0f90040100c644402c04440c20405039100cc68802c0e00003920018001c4480300039540d01e541030b4849503181c050b20041b210310b051014040c801d902c0c0151000000c1c0051110305000449100342d40c01c407025aa074090480502e0964094a01c1000d200e880c240459007804045071201d07506428110301d4070104250304102d403007034880f1080724207172101005d1041c2e000901849401042c1500c40c51802d50641d91452044a01030081500c5c10f55229030707105459100f004180745680702c1c4000704178003940f2400b44050359444401d88180758 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 396005809 1250 396004559 396004603
    0x60609011409102d0210110708030c03010501140a050301061d280602070e0c0703090306090c1701050423070f1d0f012304020f0d0902011b020105220e09 67
    0x65004c0c54079100640e0740944030030310241034404000c0c20f511541c0d003034240c010b0101e01c0009001c64011800344191140340e84d01c0398035201c00109001e92050074646100300c01c0c004074202c1c682250a072410352300700d41451b032180f00441c00042401d102c4220241d5010f440c001985520b42d07034108180b200a260b2520004280c1d8880c07405981d90070380c5105000412400c0c00029800800b0380d809000d40d40c4c0700389803100501c0e5032a2601380580710031510903540710798801020022524140341a00c9061072150090080d8540350710386046541205684040c2002c80400c01007041c0c000b07201d290702501000344140101602d0780061040341c032611280c0792a01d84040b010940102c401c0da2818101d4180760303a1003811041c110608251440a010603581080d024800002d648248030090001642440000501aa42c070b000040078003189819400c02d0001005415000d40d920404544600740d6201f1a90114000e00d2646e42020286604c68441156120309002c0021800b04070b0314075000c0d42c40418648 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 396007059 1250 396005809 396005867
    0x5040c0e0108010e04021212030603070905040308060f0609121c1106042904061b0503131b09090308010608150901031202011d16090506060901140910 66
    0x3401050381425001c100104010400c00300382529441e0b101d8070280140c1c0c850121155498640100e5400348051150701204024071400c0811000d401480503010500c00c60801d074038054540e0740b002c0c002ca40100501203113644203031503c0b405c40c0c0351624041d058601012281c1922070301c03180034448088008003d4015126001c0c824080b414450540b240509956100c03981c914801c0da0046e414824903102c0d032080307804040c208000d01442a070007042d012401e124162041802211005600e00c14002c09106100480b448104028038040e80300c000e200d0304070041518110030070b5050b030203401a54148628141015481049181203840c10b80b50f8450039103801866003692a01c01d132940c1e8001c40d81000400114020b50001c035502c08141c00000b443c1040704481ea400005066440101c640c03103003440126802081c1200c03c010724000104026506050000840074891140014100f003900720b1801803100c1034000f120101500105020b4014800d403c01074605411410003161310346e12805000c0c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 396008309 1250 396007059 396007067
    0x8041509050a0305031912051006031401380f09031905030904020306120d0906020d0503090304090504052b080610091a0c0318040e160509071103120105040c 69
    0xb090301e50150156060245201d40f03004490030400d182c1c0d08000d02950001c0c00c41c0a41c0c450a409928540181a006420300d0409801e44102a2411498040c054010080114200b00c000c0c1808414a11140ba111402410740c0d0110810b01810150580c001000384d8085981402054416000d41c240c0322001d2980a10510b60010180e0240841c0c00030403150050703241c9980150361200c2e001380a01d00320100c065a9600d8621134440082c0492803213141802700e150104482d4155014074a0154a10328210320304c03603124001d620804420070303220808241040000c1c8000107113260b020a0302905604504d1a505400503031404520200d440341001c2002030406039402d07070031005c1c292200c7c005545006103181c0c02060b912030b0200f80a405104142001005000a10041d64005c820b95000207405003080200c8641c111410055408011844100302070891107204549080307940010741d50301c541d4150f030b4245d580041071465001c00102c07280091095903c050503100c040c1d800300038120074182c0640d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 396009559 1250 396008309 396008329
    0xc01090f0807120804031212060504060501050f0322030e011b11091801091407320402160302030706060b0405031f0213060801030b1b1b01090804150905 67
    0x244240c12150040c0b012800c0003c64816a0784540c003018607156a0740c4a840340c44052001c000700240d41340c41400e400c8081c1d4010900030307200031030702000414904000a00b107480340300c1c0710025840000c00020030003a1403030b078011b4086103600b02c0440d4144540c0f17401040007911001c1140842d01030b0321850260070b4403140000307043d40d110a141d8507078000c1074100207040c80300402d9406600c0c14100c0c030581c0341c4030a01a542c3e2161203000e520008283c120403503820f001d81e83e00401d40701030015030b8000039100c08003003112000301051031340c000300034100b40440c010b40701d26926003000d03103015520041019070020042c05028041c400c2000826112403812a00f8411413041942c1540031341103820480c4c1080000300204030b030702c2c00d0042c600500c000003103040a10a0340224041103401004106100050168a038410156414240c080402015080590190369125025a20740070850713807180300c00358000040103801103501c54480b50303104c10310b21600031000706e02c0000944d21080080d1034104600a6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 396010809 1250 396009559 396009569
    0x1803031109010c06021803011d01050609040203060c07051603030908010b0910141912051002033303100c0f1701030b19090606090509030901020c0f01030204170c01090f 74
    0xc80c4441586030a8044d40003008003200f0706100606c00416a5000d2290440c01d200c0c0440800d03250801e48055402c5407c010301e26409460005c003044016a00800c8807640000940784142e2114148e0400754500b500107140380e400c20031102c2000c418103070001401000c8611802c001c1c00031003442020300040e48015140c44d0b000c040c1c5000107202c0903070007541103c104d06000d4580f01a140605949080350b4520f40c0c05416144428215a0184442800812000040d4200a610714141810f10000d10006001c1c0c8066100303103500c40414034200b440313502402200060843c2d040c08440c84e0b8030001081c0d403117aa1004585052a0014418007460812880c06580c4c032407841503030b18680791070711800d078000c00608089410801c080c203031003003d201d1807000031301900d4000750990400283e841101e6010b032008590754003e01c80d04003241c0c2d00007070786840010b05a071410103004020300160302900540e0007107144040c450115212000c00041c602204090907030355840709c10b5440200014154940c062 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 396012059 1250 396010809 396010817
    0x6060b18010f0e060a02120f090f030604111c02031f0b030f03070b090102190c030206070e0d14030c1e160f0e15090f06150306010c020108040f0501180303110901 71
    0x300650f14500500038149030701c01c500680d80a1130500703003144542c0d4401c2c1c51001e81c9030404185a82039040c44410541c41e0441600100750904040c0c071681410810a1007940c03041014104a01c0c8003081c25214aa0050340501126040074502d5404a5452916204120ba003460b005420481b841e00196004a200c0780d1405540751003156280c05244440003011800d80f036400304200c1d041031031075100303a070301070781c00c03030b551080c090308940740c000d08004001d404c0104108030058211081d5807030a5812a440f54042d0414031000c0c4465003480c1140074140207003885019054a03408540b00b0702c1c00a1180e66542c4068844417090031386542d00b98007090044c14001005101c00b4401d0b070180c0e1012035080502c20320070300f42c8544008002a00884121045110407161500388000760410b00d45010b144410000d146041d4901040002c18020f0350500280c10065050042410b101c5000c071500c07807541d0064000d0142c030030203003080c40a12484035070403400a8030b1300f04a030194100c4802a918401c205a513 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 396013309 1250 396012059 396012077
    0x30a05070f0e1309080a05070b0901050615090a0306020d020d0b101b03020a05010504150c02210d1404050c010f020106121101030f05070206010603152603040306060b18010f 76
    0x510400d44030603e0108140c030341d02e00e000700218403807034050043c810599440603030320000d501d0036014a07240544252816810102800308968410140000170144030740744c80d0303c881c0b083d40011403401d869840a041c6a100140c2e1104400a80c1c0007005002c0b9091f00a1111081190901501000b40000b80b030000d81007038420342c4a800207040380302074a40a841180d814490607283c3d5400c4400036135080320b0345258040c0c0004504007038003d004613207010f40040d000c0c7c800d001d105400300060700210b640d00000d0005064144d00d041d507000c0c4628003208212070507a0319041c44c0c5a03940d01d451043c6540072420350386901d9166881400754605440320340389240c4403042d00c2d0340d5201644008007036550500d0b4503000c0c20b1000840c203105040c45102c440d130003400a9403500b41c0240440e60303240c043c10310400c012042444074112913020700011100f144180e40e05880100f0700142107000702e400040c5198108640000e280003c100a0003101e00340300480caa0a601960054603003280f041c0030311011408510b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 396014559 1250 396013309 396013337
    0x709060e040c0b0c0a1502031803090109031b0f03150b1926150402090a02070308010b0304030c080a0203070b16021b06090d051005070302090310020d060f0b030a05070f 74
    0x100a880703024501d4007101c1001480f507032601c1d1806d442e6003288084503030101c100149542c100b0590b8809005c40341c0990300c2c20280000081850003d40405001343c8014a106000141d0100c585801484040c40280e01c2c15101d103000390406860541d099003050401c40d401c4100d1402e0803a13400c0080e030f4080d64102d9185843c0300c000354000d00c82c2d61702d5002d511a118020b191041401070003060340400e10500954070301803041009850f0040c040800c0c0c244103001c4400000c6e0016007041c1994503a0f04296200e80c1c1e20318085541c104580b0000384440fa000c15003d0741541c00101610380c07948100c001003000e036598440218100400e20300d04005038403049001609800c55180710505001c00741600d49040c000e1404103003140c025030012501c584c484c81e00e4ad4002e00942c17107560f41007465860258940075103000000c1d9907143c241c0b46004040d5000912480c0070a542e032000c00204504403402608a59400e0300f0945500f08860551125003407400068482d07221355941120301240c0e844112001c0710304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 396015809 1250 396014559 396014579
    0x80712061a0a060f0e060c0a03080a05060d0f0237080a080a0507060912050a20060601212a0e09180304030618020a0812040e0a18050709060e040c 64
    0x113407020703041c0716100a10300d0300c0741c4079207005000400c1c401e0002d0601c60454940207050740c400a1808004515100c140080c55540210840100f50411100f90301501e0900000d200700e010040c0349200000050581d5080d24021580c014900c100c04003000140d0f5961001240c45408404000380803100c100b01a01d99540a00040c08410303003d0a40040c13100d51070f543d2500703108040030aa0001c00c01c0814950701c0194040c1700403a4815081242100b002102b441650380c902002c2d0030207050000c140010400703245608031000c0c242501e03160501c4000c1c00801c000c013000744c20341214048208240040725500340110104442d41e60040c02d003c10690351601d40c200150083c058650281c04200000400b08089000d0310400308001403020302c2e45141031041118282159102c00500e40000e2003601c030460f9100240c908a6250001c806620354502d5600301c004d020594210201d030300c2490b8a1018414001070007829207004580800140d602c0300003140860100712002000b00001c08000c0c4020400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 396017059 1250 396015809 396015827
    0x403060e010b0a0810060f081e0a060203040f230705100c02190e1e0708101502070e09010b03031c0b15070218071d0a080712061a0a06 59
    0x200c00042c294400704000751900e0100e91010000e0751101d2440b4062104a1207501c000303080b0f5600c2803c29620b030060713160300e82c140d8a02c10703801103486285c40744c210b4030280000d0400c01e5009200311341d00d18143c5400d031218082000306544490102034003400ca0b4a001031404088281a001010002c0c504002c000b10707207000b20140c0c010003e407602d600f40180c0740c5000c0307000101072031858a1005428088030071003c100003000c44000c0f180c2902159400c81c005025150084024900900d00ea0b42d01c0d080c03440c040340c183c1d000c01c159882d440c140401d0142e002c2003030000c2c4e03440040f5100161b103800d280d003400e80c1c00307038103000c0da242c0c00800510344001d14480e142410b00601c1d0102240d0b000c0851300140c50840110b1210180f200d0000e036183c11403404403401c00c16168100d904580908203a0f000520f444500b11156025481c810b0300c3c041d0960755882040b00420203901114240358642c400003107192032800c011a8140d080904540c01c0d40c0950300003250f00c0d00090103602074145070400484010359 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 396018309 1250 396017059 396017081
    0x2205010509060306041214072f010807050a0e0901030609020306070e01020d120f060605070618030e0f0d0b16080105030c1005030a18061d0a0b240301050403020a05061308040306 78
    0x10318007d04048400c2d01d000d030190724003410104070f2a000e5031800c0d03000301d061f0315040f04854415100038509a81c01001d51508540b203440d0550b03d030285600c05491480d9416200c50384520000000000c01c2000c1e08140340c2e00344241c094960704d8407840029030301c0e92000020341e405600000020400d162042e85600c4070840980000708400d1168a4032004841007604404001107000400606001c1d05005141c043c5281c13980044500400752401000ea1080303842551040c00c8170988501e140c0d03105c01d010600385400c03c0000d40c49051041016296085038003d00001c54075040000a9524001c1014024100060035444400c0d10152040f60140d00040401d0045139481d20030f40d10f60094a94110300c214401c00c0e00060078201908140d0b141d020310195001640d02807105580012210b0300019000030482c00c0c02242510080704584003243c3c003080e02c1c4c0e09980303408100014541d0001d218221a40108103641030342e100d1400300791500e04c40c4030300906038100c1080b00304001aa079900001d440c0c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 396019559 1250 396018309 396018317
    0x3040b07030c08030a06080d02070602030307030f020714070501030b03060105030a0b062d0406090c090b3022050a120306171b040911090603030922050105090603060412 74
    0x4010b59142d0034150405d8903400d0880d0742d140000c0c440500104004245205076000820829150000c02580c0780320050070a0101500c130016848020007540654030085d6001c0070712426140001100c9a44032007500c82c3d140001c0c00d004d681d58050a001c0f500c43d042c1d840c041c0117003024031007035225648041005810b4035085415070303461400d200c050b41010818500446048408058481e0400003507030035541100d40d0007850202c400800d80d40000030481140c0c62103031401d4848614a8a50b0420840a04481c03551110a22083c508074416498188a401c01c02444000c50340812030300b12030040c005c0b03002030065000c034603a8804682042c5a000142d071f4a41b8000c10400c0c0c42c2c4001ca10b260b2101c11030302d52142c1c0b000c5064030401d605114185221102500c003040044401c0d100d0051424009061600920b81c64011039201d803001d00446038951005003a080c01540107010750500804da140b08030780e07220302c0e240004c5803610b009010b03e03024080050080803540c513281c480010b41154100301d90244 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 396020809 1250 396019559 396019577
    0x18051908071202010209130204120f06020f0c060a06061704080306030313090903020705010806010c061e0c090e0c040e0105121c032009061207260a0f0e03040b0703 72
    0x1800c44100c55440e500c0c580c009610361b075032002030003079a10701509242a00c60040c4800d20888158a80d01000e16070401da03c50394600f03180c24003500a01c2000c0804203400000902d414080c3c2d00020401c0c01422440030402070907940d800222203003621001a055086003035030114011aa0b444091074101da4010144ea20b81031310090744102c6201e15a0082c140c8a49800000060680501c0420005c01c420708240582c1e1800300e00081c02c81002e41e00080040e6603e240d03180403400c2ca9482d010780340d01894010000c1044000c0b0140044200e4461a4104001000055281c030101000e40d4101c545c1190749004590a12081000d07101d201031a01c2050b2140b030240c0408034101d0110101040015100042c00340011300100400d4a18581c0e004030076642000080c0d80d545a40c0c0031282c8045010402e154140c440d0340080b0303180103a00100326040c1300507911a91801c9900c150b86401070303040c600300300407051000142100782c501480341f407405600140010400009070b03074010030659210789440000f03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 396022059 1250 396020809 396020813
    0x1110030609050703090605091204060c06020c0a11030601090e07171009060f0e03040308091017040318050f0a0303030c03150801050f0c07120e0a05060c010b041805190807 75
    0x11200c2c00c9a2110000307441e091540f0620080e48101d907007056101c0094440890321100c905030920440c80f41104000310045000280043e40d0b060359188180362094901e072201e00e090040000340c0c0c01d01d845120380544c000004601500384a070642290700c030360141a082e454045851fa51944161060790302d405006032600d1050464132844401903c91040000d440740c040f100031013100c400741104860341d44100000e00218409030103032144030100312507450301004810703030460790740c6215544d0100314415642484100340c0c11030303d9058032035100e0700804200e40d80c4800f000310302c0c1214194150000b00c1c0c0304003070011074441e4019500410882c1030120b4030000c414042c420301600e0750b00c01d4401382d645105204000c07908140458120b11006038290038200240c84010791403800141d080e060000400d02d1710425160a00c1680040000520541c2c5600859141c03901801031400c40c1e900c6185050b0440702441d81c0e500e804141642c0040c010260f2103e0203252040441d0170b00c5003507030811014040800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 396023309 1250 396022059 396022061
    0x40813180903022109062a0604050d030504020f040f0e03041206051501140c01061d0f010807151b05071e090603020607230d0908070e01031110030609 66
    0x14050308000c0e000100c044031400e000b07003040b400009891110720260040d462540c084402d550300c400c1e0071603041c0c1d40e0303060a811001400c1500001035a800650b410b01c0d010441003c0341b002d10442c00350050301ca1410401c7c10440441c2c1d4226070003540114103048000f405e041552003000c1402c0815030016458003003405d1030340b440e005580305103d00900c590038402000300d03601410f9000500d0100c070080700c40c0c9100000c3c10511000104042010010484001002d42504003c0080003e1104a8014010407941b000d084008685505204041030b00008581400243c00703403c442e081d84001700c40c40800042101c004a10b42c988101e003041004a0401080e000e0002c0d00040c02c107403c01c02d4040704118440300d4052119408400c005250100c1017015850300401c50f0032032540034001d40003d4241d419020518803001076041060302c00c030f20b00c0f0003c19804c4010781c001d07a0044000c90b1080380e50b603068140340e0031b024000180075503009000c01c800d5041070700e41c007000800d035410b0105405403078040b414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 396024559 1250 396023309 396023339
    0xd0608060f070815030f0f1204080601060c0c05090709031e080306060c16060804050709020f0f16060f02090f031c140d0f050f1f0e0a0b04020706020a030c020307030206040813 77
    0x1c000b500046440f1f0640340082000e005241c942d07070a01c41c00d2901d80364040761280d20501c01c4a0038000d01d030301c48104020390401e40c00040d10b0700809100302030402c8100240a010b00c2d01003142c0f190740344100d80c14142c1510014400c4a0751140c0c90b03920b140e44100c20b000040e005407070307a076040303100d0b015002c0c090004980580c0060039040c0e8807040185004e0814070314000c5158000a1114410880313588194000011034034400d8040707a0035640d0307804682c56940304052051b000742000d450046440030710030b0160000c080c0a20b00700c80820711402d15008154840480c00322014685045441820030140030318030a05101e560841c901d41480c004100c1a01620384417840b08070001d58903820051100304d002c015035041400a0032240e9031510541710740302441403902842034101c01d810300040030007549030494401c1d04030103001035440e0300c44c80c42d014010350003540e00400130900702110b14103120b200100f5a40cd050301540205944e0b1100d072214002580220310b07010404440800c0820a18541d864007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 396025809 1250 396024559 396024583
    0xe0609030f060a0c08042a0909120207050a0617060414070e0405150d060b13111305010c0c0603020c120a1106090d0e011419050d0608060f07081503 65
    0x500010701d0943e481104603509610302c08188101c80d001c1c440850145403606000d5400c40100c0d6a40400c0300700ca10201001d550300800c10035062030881c10401800c8610005400c1b619000c45001c01d46480400543c04058012000011082a400b101200c030071882e8a420a0000d000007803940640152481c00702011204500464000443d211650605100b084c0c0c2c022041e0601202695454000989011620030050700316600c1d11041d03086581d803498400315a40382c1901c208004242410245403603001001101418404c4620002d0303d54058040c00f001c06038410b0365a01c955042c040280e000390082e01d45081184590416001c8028000005103000c604c41d8071810314540300d0b481c50303514104004251001640202500c2c65a164114400c805200400d0078980170703200304084100d00900a40c0d1101581300260780b26200d019030060000c0c500b00c43c0ca50300a01009460700c00d410b542d680c1c1034039000c0c0c210700107a0000da180fa2140b481a50040014031003140b0003020800040d2400b00241c240c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 396027059 1250 396025809 396025813
    0x711040212091204050d300c030207080102040302030a08030712020414040b010c0b1b0705010504110319031b110301060b04090b09101a0d02030a0f0c02030c0c010e0609030f 76
    0xd01403400c1c01003000319240003100802d0f6107028209804902444074510000740001d80884410f844100324848203100000710300c81c44c65404040a40003001120104429005030007622000300f0f5a140600031a016a074020f80104458200c541e82d445c0c10f580b00401c64401c01c9400920314540c1c0703005000401c0140408003541d40c81c3c202d21820001292621051703603042c0a6a0f070000030024542d030010961081206c488465240182034480ca910300c01c03000d00400951034001004104a103005c25118030703040580850b8162208d4103074103140d4131058031000c0d0103d0214003244044281d802d1b80603441c03c0c4601855004c0150390b4012a0035103c00340c002d1041020081001c0c00f03000f03034620582d15505022140300016090590440008080b42d02850345035040481a00c0350003a40f0000b1a014a0182c54046503603103441d00042e00100382c921002e0301410b0401001211080c070000a5420603950100a06038043c115001518040b00040c1542d8201105000340c1d11a55000d100008607500e042c40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 396028309 1250 396027059 396027061
    0x31c0e120a020904033f140a0b0109120501020723151302040c030b040b0d0c0b09030307020a080c030c180703273203070b0408040f060e0301060905070f050711040212 73
    0x100d01c070b40380c500b0030081200c1c11f8074100200d444070700c07140030321034004003d07160004020891400482d00c184080c0c1000c88100d040c1407411042060550052529a0150a030a50001070100d48268261004c0d01d84400030344c02003444d00c98800844110b142c01213140135600a0b000d4651b03000ca01510700c0d80342d920020903038802c4a2074807402c00c0d0090122113041107900d0320029000d956449440c840c50b0103102d034410740c04181c2e1945500d04100700c9440940082003410340c9a5103170301d1640d440741141c4140380030f400340b9004004903003010101d080152100c00c4020702c0a40d54000100c000780309109074140c542500f0084c02c0301d41c4820300782c01d10320b03540201c140c04401001c9001c0b2907888c180c1e44608180150102400c03988482d030100030340343c40c03c1d8420007a0241da02d6070700388548e1038055900202061a0444000071300103070008030701001c081d0705900a00620b6a03540910b0210f4000302c40040100c0c0c403040302c0d90446407143c402414032078401e410454802d581c120208007260402d401881450401c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 396029559 1250 396028309 396028397
    0x201050a05090420071b0803040e09101d0708011112060102070f0f0e10050603010b0d111303050616021906020d1103041b03050309010809010b031c0e120a02090403 72
    0x20304007411090100c500c004006d89081030032540e030b05c1107106014680d00c2d041c000c5011400140304008100000e03850a2180c1e401d0480f40204c17500c10403407450380602c00d101c0c001600540c18040c500b00412511034040c01c0403024000b6542281d0b0081c10380b4110f0144d04000310712840905000800b070042c1d6000d06c12090b0810485003900b21000d0072816888180c41002c10145d90b54030704607410b40d4078285c60700703450300c1c5103001000213400c512549040e014008500c90340c0c00b0310071a100504403401340c021548562a400a5800c0c1005c1800c05e80d40180c012080e460100c00c05001c0441480b48510740052074a10410800c0c8212a034200c0b07880f40413000001408140b0401c0381041810040b010481d032949407540da510b940d44d02c10323040040d040c0424240011400c2c4400c0d403000c00c07003100141c243da00c82080034a0f030b002d8504080c04518041215108400802e003812003011840304501c0004090040d9182c00700142200c0c0180201c0070010f010324100a402103007440014001c04001034450100322071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 396030809 1250 396029559 396029573
    0x50f010b0901050d09050f1509071e0308040806071b050606220504061406031f150801020d0606140703020c12010b0d050a051c0c030e0f0a030c05090c04030201050a0509042007 77
    0x4854100500d85008c0b06200728600301017510422103602507550391000e64824103c0d01d40e80c070325900240c00e101c00803800269032100410130702d1160740c5031f40d1a01d100300c4c03900c100b01c201126448805000381d40160700051031420b00e4030300000d040c1400c0c060002040d030814240c00030385208a0742154110789404000033400c4112820300c3e040b03581207002d06103191010070440301804a07201503210054403036000c280c01800d40003465000d400048001d5640d0700f1038031f0086005e029940b04030000950210807803c4900400d04c00d44481d030782c1c1a03000e4800300130342204010f60059503007091b051a5603600b82007109940d46548c088044c92041c805003900a24a050940c10a948250310032650b03400e0345840c4620b56880f50348109c2c9a60304d0305040b4441c180c2840412241c0047c1d4007516000809020007005106407003440301c003100c078216510300065440400c012003602551000a003c1242400012040703030082014240d241c030042c00c0021a212501180824240c44612070114400300007058400c5c0412 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 396032059 1250 396030809 396030823
    0x1003060f08150f071b03051207020309091f0303031104080715080708011202061b0607030204031b0f05150d0207030c060b0a080c060a1b0305091003050f010b0901050d09050f 76
    0x81190003104130720340080060818150b50000030003e05c1000400000c0501520039913407000368220540d030b0203140c038000184d580d0b8003040d01c181c8103606410009045100d00c20740300d000300c003c0da24111009803442d074003070740502404240a60003200500002c91500c01c10407254008060304e070701c0303004c07804020080505400d801910410400221600510501d001295034203007090341511001da480145050035801028043c5204c00180140070030f02c0742e620b9258020b00103503130040000c01114000c81402c99200303405449091007804035901c00f0050391402c0044240344001110107146454041401581268400741341140030030202001801031043e04c0c8510181000c0035603514000a0910909980e01d9000b460018071400c400074080365040e2241800000070f14403400c4140e54141a890050126005003801c94010540c13030250701c80740c038420301482e401500341c03900e03206190b4204511048240d1240d0b0b085414454200006140e0301024840cbc08401030140002d0010251042c54150a08034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 396033309 1250 396032059 396032071
    0x20403051c09060c0c030201110a0218070212120a1104030503070804060306080a0209010905060102030c06010b0706111606020a0512040b0906060d0503030f040203070305240a0507020c1003060f0815 87
    0x90625440001030704000114051b40d409007050304004580b03461041c81c107100d606c030094000d81c01a01c02c2d10b075241c0151b01e4a0044030b0613000e4401091542001102c18090421303a407801d6100d00b0041604800b0715403051071100700c241342d0545401e841342c0390b403880c55020035011a03001d5400102000b40c039605210302c0d00a04903600c0913051b612065000140100341c1802408280c1d81d44801040160f0700820880c1d0301ca2071130100348c1d41c4641c0d548480c80c000c0d401c1540706175041410800d03c3e544c51144081261036800c940078110800e2002a103d060094001c21030303407024842d08020040c0486213540b10103102e03d00c10065545a4038110800f107081c080041d02241c040e42000381c8070000184080140ea40c8440041c0d4204003581e1503000003840c000c0617600242041c081e020a01c1c1c002000d030301c80031740e085030a56120205510741c0503441040707070401c4802d280141c002104025003443c0252480c0001d04180c81c010415507100c4001c81c05200a40d400a80c25501c442c6069000c29960058154003034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 396034559 1250 396033309 396033317
    0xb0a0918061404050a15060903020f01080106020d0f180e180601060f05250818030a0305070b040c08070801020c01140f06100c0b0c030a200f0d020403051c0906 70
    0x5440c102c0001020201002070500c583d0b181c02c005480c01c0742c00d501c2840c0c0c0b060001b400c88403540e943d4101800b0660b4a010a034090910802661119402034241c1030498800d94018045800f042104440340e098615407001045241a580c402c4a05c040c8c5001c4003620340c4003200c40c0e0038240b1a05802c1c0610460042c2103258000c3d4004000d07064005404001504460502d15507612520080c01e6a024129441d1180310b51940442c1c014001d09201400107994144a0302c2c0c000200c540415646844c000070003000a0020040240000d642c40381603504030384500300e401c0d603150315400364908000c2c01d80c10004481c0c0d0b0200d00a150302e0024050385014041c10f0300e02c103403c0e040004040c60f035100004d021902440b40a4244c0013858428044120389507080310b580483c1d4104840717a800964020341e8080101ca050005508032059010054190861800e42c890b2621058100301407541e004075210000d000d40c203020000120b0820311400030070845001800c08a0001070701d014000c1145600504100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 396035809 1250 396034559 396034571
    0x30c010804200103020d0204030606051912030c0201170c1e1213030c06020406091a161e0506040f0501110f1804090f2105120604150b0a0918 62
    0x30602c4019001048250014010080032000740142d0103441740400280d1001e20010780001800107551042081e0340080340d07040d803c61400a01c403800d00509015081c0c0280f43c00f0030f0301c4006801510128441c3d031040c149035040c9030020030000c40c070f0b103002c44110161000000301013030303280b0703c0c400061103403001102003d08050640c0180340b001c0600801010120580a903403400345400352a0210500c1d900c010103555a5031204402440c03085203215031348006190581981040f0f82103015114000210491000003a01c0d07510303003550024140000080310541c0502101c0403c90038004544554002c0d0074107214003c043c41c146d42125210b010b0221000c40c18004982d80d0b01c0d021040f0340d07216444452903a027103c070800010700140407000c001400c810021043c58108101941203881c1804a015182c0682f481d000095403180314080000d02c000d044403000440c6450f080d0721a40f54006002080707600aa290104061281c2c411141c0c00c0200f540802d0030011030381c9290380010201e031401401d00803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 396037059 1250 396035809 396035813
    0x15110c01020f190606030c0807051003050609040609060f0221070e0a09050a02040e040609060e0628060b03070c050106061b260d0e070b03130209070201020903010603030905030c010804 81
    0x101c3c45608520402d04003481111814003049030043c60103180c00c543c03410b24255940424990b14039203407240074041c4c811980064801401b03071254032b10441018210607071995495542034010310990790101c40542c4e49660409000d81c092000d86100408240001e403c0f202c2e6011f14801c00000605103c1003000c7c80c00425020703181c0f54120302c11225008400314040c0c444215500180c0180d401101514000e0380c200018024280c00040f00c0c04d01a2904001e02c0b14a20100c03070311404110b42000c1c00744c2a01c1c10310320703000b001030b000c1d04000d0074422000625280c072228500091340c0b0594090000901410030302061010a01c41c44004240b039040c8202c030410b510001e022144140c5201400344c40c0140d07002e600046104a0581c1044140d840c895a15031095040c000142603800799103c01d0b01c907014000c2100412201100c0c056000c0014081580d24264208907031400010b0126046540070310160405071002d0040401a41c440d4803002076590420007411711704a2103029060400c4080814840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 396038309 1250 396037059 396037063
    0x82101080a0320070306050f011d0106050a1107050a0f05030d030c0f080402011106010b0c07061d0d02010c0b0c030708090d0806150705070314120a0e0103020703030615110c01020f 79
    0x10075141c0d003c040c8a06841c40071405400d0412591000e0260750500080106034504100d1aa05842d144c010000d01015603102c2d903811004d0034002c0d4400b19100300810040b450203010050104881141100d00080e190b102088801c0919884078030a4070680100b0700c1140390600c05543c0070f01d071038030701044915261040184a044080c0b050018000c58070003050542e4420380f1035850000054084400342e5a43c0c44075003086030b0003203035490118003500c2008900d46209102e0b1180003240605406866005c0108010502c80c0c1150104d05000e0031141c250006505440d0799481150301941854582c82c0004010340003000041401c0300d0364000041c043c103001d811245280c0c00400c207444543c013845201140250350b00c901c40700504940714581000041111102c0d280c0442c01c85e500c155006000c0038030100c500d5014044c08140420940c0b11002c045511a5002d803910750300916020038200d95540070b0101c1408540d00400004100c0c500031481c11904000c40c81002d0028030003000d92620b1010310503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 396039559 1250 396038309 396038327
    0x1f110c060c0d0608060f0a06060c0c0b0d060f0605040f06080f040b0429010504230705030a15060203030f01060504080c120c1807110d0f0c020d082101080a03 69
    0x28102500100d1040c004261070f074050380c0584840000c5600070700f0b1486480f9102e0404441020165062000100303074140319001d4042d0203944002e015040c00c1c1000304904542d04400c440750041344c2e0700d4000103080c01c8040001001004681c03555640c5900709845640070501541080060040100501c20781005a145559009801103030751100b540781c5103003104400d042c00b80c024420005c0d115403413101d10401c44456040f40d00481e02000020250365002056181100380004164030303c00000c0d00c000d005800440c0e020f160400001802a6801e04e480d0003000c0c5500100c00683c03000c81004900c00101401034003409103401d105090901d058100395407018900c0180c2e000310000c502c1c0c450103000401c4103000386500100b46480703100d281c0c1c000c3d00b01d400c0101ea80d1000210f031110184000040410031062504881c2c0e91441d400c071400f28151441c6d400d20394101d800c02c01080c088000b0540c410301410003907010381c0b25181c060080d000034580e45170042e0403071070598000b01c981100083d0800081 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 396040809 1250 396039559 396039571
    0x406031b0b1306030e0c060406170609060d08031b04030c090e06060a050d0305040905011e150f080c091203090120060103030806010c142a0a0b03181f110c06 69
    0x400c01d05c407514052410700355a000065040180460049200380e04602c258807031b0b0b040c0d04c3c11810356076a903104110403a482a41e03203036003082c2a001c0d81d4000c900740c14021503210700c1040d40d00d0254006402040c0140e44103900698078506004400d00440a881c064001034a03034803001070001d03041a20010b85110050320a4520440d240b40300d800405000b6801c2c0c50082c08190b4040055603510f9103091015070080800c81c2d00c1e049907420202e4a0313400444034040550260351005840304c4042415121071401900781c0716038240038448000d8580d90842250790b0803560740055a2030300c12040c0090181c05903155005a800390600e041d400f84c0d00002107017030440f43c251411461540728540140c2d0700204040c001361913103000d520341d10802200016a1300c01c220242c1185e19a2880002c01451000044840c055104030009010410101d4410245811920031003d080c02180c0c00c0d05401e01d011040c50502c04001441100488100c09030b1140440100001000c0c80c80e2011000d022515510700a040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 396042059 1250 396040809 396040811
    0xd0e09040b0a0f0f060306020702030601080d0905041112040c170706050315120304120b01061e111c03140a0207030503190906020703080f0916050d110406031b0b130603 74
    0x307200001c0f030464001c082080c50f800c1c2c04000690300e81c10210040c0d030182c9020780c000d20810780000307a600300004d50a01032910658421040600303003400c0001500c20501c0e2105040781c00c0c80702c0c400c0d4000600d4414021032081c8900940306103800700c40055401072510240054200c2d0b00100003e9800001f1070b40e00449240829941282d240001141002280345c900308501c4003003000700b241d010964011141d68080c031200e50040e0f9071001c08a64030104003100c0301001040c41142500f013801413641c06500002c05060b5440d404626003000b0101e40491180c00c0000e8492400024011150000c60340180280105514080c15914040d085200c098243c03071603e80000701250740d00000d5480b050b401540102c05641d50a0a4200100820b505480e0078039201380000218060100020b070000c00d852a0740c03202c1c05045e20309002c00048110740c0400391040380128844510301d43d15880780c44080d41c030901c42c03c1c030001101000c0d60200c1c0901d42250064030f108011b110b450f145003012041c00c0321030900d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 396043165 1106 396042059 396042071
    0x306090b010c06020903010b0402190306090c170c0f1209061f1401050c0106030308240d0b090f0106090605010219150506030a0507080d0e09040b0a 65
    0x1640c1c00701e070280300300c03030300264803500607090080004000148a03a910700c04541680e1051894a25039034038070b95000040c9406104840140410345020080c0300305402002d030441c101c0329000703c031000048000501c20341c0c00004503044e00100c2d61031036403610001c101241500d00e0655a68445000e40300010340b9007195141d01040090740e04061400e50780c60280300180006041580b6410800c0802c002e41f07002d9802d0140400451103950790024500e4050010407030162a210034440c05015801c0d00d010f5983c0310042002c05a40080ea03a01c282c2c0c580d464110b1030b0520f030f640419640c4d4280f42e0000303040a2241d200c0021603400781c0a86d84c4c108400c95405880103c0c00d0b00007466451002002030050000b54050380d480b040c0601203503400c0344d40c1e80301c280c9844850307440403060350f20a034099a0340690040c80d2400138903095601d4445400e0690f070740ca5207404001c003800354041d0b03100 = true := by decide +kernel

theorem cover : BRFrame.Cov 395863309 396043165 := by
  have h0 := BRFrame.cov_init 395863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 395863309 ≤ n) (h2 : n < 396043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
