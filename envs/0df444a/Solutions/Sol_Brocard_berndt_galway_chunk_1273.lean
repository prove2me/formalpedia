-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1273
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:06:27.919996+00:00
-- url     : https://prove2.me/submissions/00abc198-caba-4b38-ad4c-d3aa4ea03934

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 228776978 ≤ n < 228956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 228778228 1250 228776978 228776987
    0x71205150316050a0608180d08010503010c0f02030d021c022221020d081c06050a0501082202180f0f0105060304020d03030c090f0801020c0601051804030e011707 71
    0x403201000c50554001e0a0b40c440504041901881025040150203204000850241460652040e8101100603039140c01540880c10500d00c580d1020100d03141100600190078240308500108455091900b42c03810985000303940d81c0540d0501d201d1094001681100103a404610315000460298003136483e03d102c2c1c030105003000481504969164401400080d0541905990341344908442c185840709403240e40a000d066101c80340d0546000c80200a06801e26051505020442c0010000095020f040104000704000c0d940d102c41e04100300702c0113010306040d010050310141da40710102400105a24804107042e146400030900030a44010300304030740701c0f94078200d0501c604070741480344a241e030700c90041001602080d50f000c6e4002000d2203802d070000780280c3c01142281120309090003215513802c00c680c049030745d0b0b400c001c0d1140d40121721405408000c01105000d030030112030380d041080e16203201446060005002908020700080880d1141c1d004040c0c40c40f20a00d07841045145241c090800f42 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 228779478 1250 228778228 228778261
    0x6100e03010612030318031e03090b070903020109080d0801150c0f080706050c0307020a0308150a1d070806010c120509040513030f0206220804051002060703060617010509071205 78
    0x1000300f03050004e20b21206c50440f51450071194103031544041403800700a0341c6150040c14400c0814150790f00c1c064404151194401845501d0321b5554500c01c600794800101180715a5000d0000c3d948800b18504415401142c4181500c072a201000c00001100c982102c000c4042000038010004405904081c4a01900145101c03805000103000a8841c132050129500c070071100f000041c2c00c01d205410000703106408d030035007200ca0310304615807a242d07103000203662400700c0d803002140050381c24100100840c00d2140c580d1084c8541443c880b24503104001a04410381d82c81c000300715180720218040c409020704203032400c0704005803080040b40b820341c50405448841305403c0c2c010a8696000c400b666200080fa0751068041a4401140840302d0501d0002c0040051040300d1211081c08040740c142c888610120200c24954020a6941000e0b10050200c1306a42c111001f00000c07500103d000c051b20180340c3d41125400d84841c03002da500c0d410300b1500d80c650740c03044602007030600092210098410003105c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 228780728 1250 228779478 228779483
    0x20c0601080706090e06062b0b03010b0307031e060f090f0b091f0e0307080d02121003081207020f10050a0c03020405030c04022803060f1d06100e03010612 68
    0x480105443d00e0040d20f001500d031040c1c00070302d24044006040b41c102076010f45882040004041801c0b5107000d038900c1402c03031040c019010701da996080f9000340d00c1d0034064840f01c110300b60042e00d10a070a54682c100c0103d400710200030314800c8070800d00100720700c40e8042c510080401c2c0c81000b00310482c1c50480344129000506840310b500c4030011400210020545440b4085004118000003102d07400c03039006080d039010141c2c40c0340014001140824401d000a0a424103c07480050b034544003188003528000002e801100146105001403000031454021110500d0904003001d09680d0345240891411b01410f02c00c0b940c030700078501c1000c84824140c21041c05050481024000b0ba042c50904800301d01030b5100d203a500d54042d031041c01c41418650300402c0003100f4090140d981000328803400c0903800d01c0400c01c00c0080d640b0001000316450428103140134001c1008007000072845014000b080001c003610151040c400c0d5100f40b9107040c000c06542410240c060028454a55964514614900b010006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 228781978 1250 228780728 228780733
    0x60c1e05070b0106021b210a080405190e07120608030703090f060c150e07030b0f04030201180201020d0f0509030f030424090605180a03080918070905090910020c060108 74
    0x110346036001060820f2101100c80324650134624540400000075054a03c0702c60940d4a04d07011900d41205001c50234155000b403445540d59031a00b018010850708040010314110b84100083c0520800101b0150f004000c514000380d500c01603642c446d0040c4010703407007100c03a8800020900100f54100c0c0c02001151004841408490f030390b070100307a0301e151030b80c24020701220f02183c080903030040c1503001c0c10f0303105800011100e4658032130703482001010040e80d01c410140041c00400082682c240200c0109120104030450341910343d40c0040c0d511200c441c1c854040c0300703111020489040c440c4043e41c0d4464401012551810075101c5155241d62050090748820860340103070080c4600c0d8514000300702c1c80c250344c2e160f640511b001d50031540b603000041e4208401650841000c01c50f0b0b9500145c5001c0c0d07014000b4aa5500703140410440b03941c94288244414030801c1040006040c1c11640b8082120b60039500c081b11070ba80d0701c1c0114241070710f240c00e01542c141b021034000201a80014400d0684594008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 228783228 1250 228781978 228781981
    0x403050f0f06010b2a03040b0d051b070809040902030105070306031703040b180a06021c0c0e060d240f290406030902010c0b072f0a060c1e05070b 64
    0x1101900c0320342c01d0048401e095000c00c80306100301c900c111170100003040c1e402c0103400c00e8049482541142d21036400908450404100580410664440c454001c403c0d4a42e00c003086080684400b02400781c40d1740940301040104801c006620b0b43c0d0009a40f881d40140200194a40780d1806030040402d0f000580304aa598904a25451501000c490040d0741020800104d552840744440900788440d0746c61016010b107540b1540001c41e14000740803c010390344054820a083e004549040307482c1c40191408011410017404d01d55140c110803924000f118200c00300f2605046c0c0c840c45440c1b02400160302c04804800400500603007550b4080713050383c03207400360424150124801c6101a00048a206003240c0d003c00042040314042d9101c03565044c418188240c4600d4241c5600d400031004030388070804264865034500c0d40111900640c40480840380034078502502c442010f5680340302c4103500a04883c1d864a030040701038016802c4030b080c843c590506802810007000c2c01030494001c200d0803908070b82c2020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 228784478 1250 228783228 228783253
    0x7060e0601091509092d0c0807060e0910090e070f090c030c170708060f040504032f0a0803130803010611060a050402030a03141c09050c04050621010605060403050f 72
    0x40c4001c81e034000303515100b03100341e600c402034114040302e9044002c1b1040140d04400034a41c090340c1d1004040d41006801031034a000000341c00e501078182d40302d2144064004108184c2104040c0c9000e070b8441c800300291b0074440704806850728425030450880118200b50004000340a074001500d140b1040c0e4041c002c030751132214162154000143c7d5030704000b0b0190f00281141344034600b029030040c40200004848101c01d0042402c540040d00c095000403061440b0041103080c43e45070450810004100a00c100c05894445803900d9852500074200c103000404140c5403507241d9210100181c20a011551b6540c1d03401010f8125080090140400d00500c0300140b01503086205951181e50068064403e1a0807584d04881042d441ca10306906000180038064a60928030945485403011100008044120f420010b140104401469106508190030019992140122040d0140c882c0c484c80c081003800340c4803140501250b8210b01e4210202003030000903c04001030040e1242c40c0c00d01969840c0501c00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 228785728 1250 228784478 228784481
    0xc03030306090a0906090f030c0201030c140417070f08030c0606061303061d251203170408040302271602070b180904080c160e0a0207060e0601091509 66
    0x200c40280c0c1c4a03002c88000b4400550a030402d40c8000d104100010701e44403103558aa640128a43c02030340050401e40d006011941c26200d420070042e12414201500c161505041c0e41c1881240159590b01c1e00e40061107410420800c0b452000d8151038544035101916000d1440d81e0740c004650b007007110f2160340045005030074104100c036003511141740c102030402d065484850291207005242007203025103c60001c070001041c40090403801c8403451108035003100c2e030300b00301040c400381c1c1091010900580d4003500003a00301c0843c00e0200403048000c4031076030312070614034002d015a030300194005002d40d4840c004401154249640044159504030b001c1e1214008039100c080c09450303d00150b0321a04041c031600d01401c015148c0d200d02e002c0310311000000708000c074050034001e40d41143e010002040b0b25480c0901440150003686000c44001c0a1600c0c250404c0712410018000c1b104940d80000c0d1a8184850b680140c0002654001115515656a060000109040c4080c9448000150804184200c00707 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 228786978 1250 228785728 228785731
    0x7090b0a05060315120f120309030a0807110106090f1b0c020402030604020d02070804080c0102031315120c0c0302070b07030c0b130b090a0b070c240e1e0c030303 71
    0x1600c110311450900c4140240c990024040070745515204092603811707a80c0d49a000c5c00c0000e024090800c04024440d00352410f07186406108502d1b03801d00401410710b20020683c1d00494507450b161503582c440b1001030710080d12030b544500c0c140d4242100800d070f401d10342d040b403009262004010400c2180c00d0280a01902a0080810000c2c6414501c03201500d810380103590400c1005000624100301c0c0240d82040341d21110080740d0003040071804122480c41400304058442d42800514940708200d4003100b040759050181d00c050280010880c0c02d028810582c41592001e2200e003002000359541020340300004069040380144900301c0c0c0400d5000d480300a82c0d1440340c2c907494450225030165a4000343e0100140700442c0b8819500240d404150144001406141c800029007500301403400e00340d000290050241c0c0c2845180102000080d0755584440c155a100e4110310000382151070ba03040150007000424440d0b81f250700c0804180790b02504030f80c1c01c44886d403011507008084c99000d15442e40030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 228788228 1250 228786978 228787001
    0x221040308061c0b090f01020c07090510030c0e04061e09020a050105130b07050309220b03070f06030203040606150f08091203040201050a02010207080f031806011512091208090709 79
    0x9243c0035507400218070400141d00210540c01b07840700c08100400c1d00d400c9030040d084400c42c550080d2030800c03500d4090321034941c103e034800611000c16800e686480c500000c2d00c1c850311000c860000009018001c250f0712100c0d00390302c0d131501081a0300015402c10302400303140905074440d1500380c0d00044c0540c003030300454020303a1070f0355000080700d4600f50600782c440e041828203603000c1c0003c002801d455558603450702902900501e2101110341c400e00d4650444180c205100d000703500c6000c051001410a441c51b404a070b8685c90096030300e0b907540c50400040c000c06d80c0003240000403100380c00c1c94540c115410719100500380c0d50f8104641c1c3d841c03070035690342d81b568264a00740386810400309015510550042c440100140000351411106a842e55140c0c5e009880000c0304010100c00d00180340d02100c00b0104920345540186800e5060005c00d068982e48203040e20288108121001420807940e00482072880e0001040d14055012030700c0a4018101255402150700400c02c020591440b5403251855615 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 228789478 1250 228788228 228788269
    0xb2a1801111c090806102c06151605030309010b010521070c05060a09060e06310b0a05070206130507180e010f09030e040204060e0d020103022104030806 67
    0x10031100007010010103480000382006550200828003550030420180075001c1e900020800030300d410140170b2242c07440901010007001202c2c908840007915195543c2008c011100d800200c6001e90320b00c10280305003148085c04112820000d028807402002452107030f01c4641c000d01606009c2c10044820f80f00e5034001d03420300c8264620554440701110705250b0f1045540c1400440202c46444a034604982115801e82c80c0e900d403d030308802c02030075028007101c60440317100400c0c00e820902105513100660710000c2c00d045441c5207210707503d03003c0f9042c1c81e18116040000d488042c204910904042c1c60110382107000f62042d44d0110b030000b81006901c8034201d8000b005001160309001010030070300d0200740d2030340c0165200d20b0300781c20842080c4910138089100510015620f10030b850b014104503011145c42d403007036206000c10400d040d040a400c0114000c110b0b207002124a0354401030b0000d004550301c224940e020000200c1a204a141100d401180242c6410030142e5450b4100700710b070460400c520940c003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 228790728 1250 228789478 228789493
    0x100902090414010b030601091b17070c020604050a0305030409060803090307060507051e0606030105010605040807140a1a031008060714030a0b2d030105130b2a180111 73
    0x1400710102c0c00d11103180384002007120744441d8006441d000083e080b64001503070b188000100d03104000c0402511050a090001242c58400810381c00320000510134400c2c0240b828404085590340c07c1100c000c1c01e0001e0482000d95101e051980d50ba4200c0c6c00b60f540030524003000480c0b11b410000c2901c100f4135004005210700c2d0306000e0122840d80003018220b541e1311a0806220900802109150340d0390b46160083c2601e2902404141c252070040c0e008406200e010003083c0200f80021a0314401d451500c481610031028040200340782c611039a00800d800c440b0400d400b602110590015401282d0100300c0036245920f8850098603600c1c02d0f078079800815004110980007446581c00745501c084c0a4500140c1003040e10045001103559410048219a80a014189031136080e80d41c403000060581c020002d904e40420798010580080c00c000d40300c140031100040d4031807000c450500e05800b968a1a40100814070000403481e000750802d200c2c101d0964601e4600ca5100311520703d034003400300340102f446 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 228791978 1250 228790728 228790733
    0xa0203010f0b01080a111603030b0307030803070816080115020f03040905100806060a0509061f0302090109080a150519061805061c0206130e190605030f1507031803020a03021009020904 81
    0xc7e104084011403d0545424587c012039500740138030f03001140580c0345540c1d286000a002407443d4030040ca0384148054a20409050a2f030104110381034400d4120507500ca0042340c2426843e0040c0c05403200784900c0b00160109404240d0340000c0c0c00340300f400c0300300d0140d292100380042e01c0700411110a5040040b0503010085807418424040d044070001c1c1c0104003100000d401e030a501c060400c540381c08690000360440555034081001c6000b407903840003401e13040e00e1756616a0540f4500954182e180d40d200c001050510f07801d46440c00158140890800c07115541e1918410041034900c41d10710110726140c0002c11500301100001054480702007103c103800d00719800c010181e0401040104c1e1106032860211b45c04614401440c003a43d89040c2c0400508154a00b000580b815600214003d030003010b1000f540c48400038866001011000c0c1c00c40345992541c80843c0101401c030805805281102e0241003416008606000800c1c025070941d1480e91340281c0100035102070440094225030b1410010b0003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 228793228 1250 228791978 228792007
    0x12006150103020903010510360b0414010602070906091416091a030405010513021507020301140403030f0b0303040b040306052e0f0608040c060305090a0203010f0b01080a11 76
    0x10900c014100107041c00c1c100d4010900315442100d6040c1d07980d08014050101c2c801c1c0c07000020101c00b482c1401c2000c000d52905040c040703d14070328801c040c42e40354100810540d4a5800407000c9150444810000d5a55443d0003036275809288140300030140307000c1c40881c41c0035444c042c411882050f4030700c80c069511484103100b41c42c40d01084c0c401c01c004405070003266041d048496402c010b4100c1c50481e0303c030b06090a0150840342c0180848220f02d80e15890100140c40d00d4940c90a1180401c266a45601c03580c0042030251400d06480c04012528404100826825500c03122044500100c00c21a40b100442810759134402e07402862207100e802d100800010f4000e401c516808103220b29040309003d0580310904803411100000325114050030300038080b007446818104002c00d19454014418105600c03040c0c1d01c9002801088200350303c2c1e000042c0c0041c0d040240c0810980e02030000c21184051029420040c401e0b0952180016013240100703e00c00507038041c9952441c001e109003440e02180060024 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 228794478 1250 228793228 228793261
    0x50a090e0a06090501121b05030c0105130e0a020c0c0d05062e1410020606210c130c030e160b090a031a04020a0603200f07020301020408070302012006 66
    0x302240c2c1c551002084003203281c09868024440c03400d20304075910481c40d141003500082d01d03011550700c1c21207204002c0d95600040d0b80e640c011003800c00e541d40d0618414014006480ca4201a05902ca650f042c07010194544d40200800b030241400d44011050000400024950228000e0200d40c4030340045072044209140001e000440d0082e00d00094640b10400c41c000c03030b030b158464102a440000c80383c840d41031080804603a504035101401e04c034602440003480324040da05001041d41c181d50810b6010303a82c00c000d501d010180050942d0310070b000752500b0703201600c000010000001e041944000440c00000340d58402c200200440030354850078050380726103541111644a5200c9002d82e0b00201207440450111400c200d1000101d200707203003a0040c0440c2524550041d402c00d440c015213090041300100c505000038041c0c049603551b5060390403d400c0c41e40103165000e13515510000e00022004c0340040d008003100e01c00c1c0c035101003d0700c3c4002d0a4004400300d02c182da01503000710300010700c0811103c1210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 228795728 1250 228794478 228794491
    0xb060907090302150309060c1603030c0e03061003050c120a020402090102120403052515080603100e060411030a0f11061c05091002040b07060f020f0307090e07050a090e 74
    0x1071040c0e03940d8002610081c818000110311881c00420700c900420244181c07540036000005c501e140041c80e0190b0500001e0031300d400703800c1680c2c1c6c0079854080d80c41000e0159a240c0c0040c01c5852500340500481c20076401440b04550604c90b0071b80c20205030030081c86440713242da1000042c0450003055001d002c0a540300e604e00d14110b00529420060020801c005000554007400050811000304480404200580885108001310902c0200514900c10842544961203450301068641711000441e152036851590110040d0800f00e118003090000107d043c403807801000c0c40f4000e21034140030f150b180c580ca43d0010340f51242c5070b1100000300d000c90f181110300007806800c0b2403400301d035409100c080207290031010585e036403180240000403034104800c901001d0402c27411441c0c949000103100181c81010300007030816446141d158425080e533816204131039810308090742c0c2c0749080d00000f001103000b405a40c0442d2076042c0403e082c0c510900c1665070391619510381c81005070030035010341d03008100100403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 228796978 1250 228795728 228795737
    0x9040f090b011805090a0206030403050705150c09010320160f0227091615030b03010e0303091501050907110c100e0f010206101518030506040c0b070b060907 69
    0x288000509112401d5000303001c20890f400b03076204600c0c400c00540700042e1451484c0da015590074070240e910b075400c4a4220b83c0c14205241d6500e4a0314100b81040100202c0360b917802d42500820410000040c01400c0c104000da80411a04000040d003a8440700c03c014040f00e00001403058a60022540d103042c0c4800740102d217030f41c41c03404c550350005a82c040c040f40c2c030404291210295204050204003034503000b2400d10060100c03200f0100301c0d0582c0b9040c0d0b200c0c4003c034059100301600b48034065400095458000740007804000e4800140355a07036417095584513421312812070a140400781e01c0b4007440c1030f0f81300140061669210800200d828514441080180d03026801542c0c80a6079001c1c03c150f40002d10f926440c54512001c1c08200c054156090f296066400010411201340c0c0700103d040b0a440c00c40769011112280104225940e40303810013044000a0710304800b00c1408800182d0383c2c81180709540d980fa0b6661076582c07043c0036014024000304424861000301e491464400c03111076010510307142 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 228798228 1250 228796978 228796991
    0x10623070212101503060501120201020c270c030f010e0106021506130e06010503120a0915090503070b0c011109010516021203040e0901051e1501090b0a031b0e010509040f 75
    0x80700b0f800c403151414102e0504c0b07a079004c10020003040c2d000303081c01480c410320096030007001030300041e4580c584004040c0c0704080070000705402e0035200d510310060070803100d147c4426290101c406c041d40d600070343c0c1078014209190300024018410840f024181e030705c154003604405814811503000d0ba00c018041e00e501034044403411180280610a03005030100b10b0700142811352400301818104404031011620041c0100700d144819600240160112a1071071402c1c041c608800c00c0450b5007100642006034140100d02001848100c0c0d08060588250314400800040d201e9101243c02403113445030890124000384801e400322013204031030009040c0043c0c0700700701001c40c262500381154441c0d0403003250103000d0380a00c00046000d10075164000007401c0520b0040001024089400d100101025031582510b8840b02c01a48038180745402803554260290700c480292720094047c20960048a000a491307040881000d442180524071404041e1106807030a900c183c20701c00a004000d0421002648402c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 228799478 1250 228798228 228798253
    0xc06220f0501110a0309030e040513020f0d0602071407060903170307090504060803041e050a03021302090a032405010b0d02070804050a0306020304140a0302060f04050f070e010623070212 82
    0xc000c010064140d580054505030071310b40623150b0f0040d521001e0140d031510040105006107038960041030b0750100d402e1810541c1000014426051420000703090500100d923039030400c1089003403081002c281805a0703a00d55101c6070b0440720030303150344400b40200000750100c090100300310004642003411480c0c200c10030b0b0346880c0811305481050340042c45540c0700090400000d0b5207111041460354031040c008003200d24080009000c6d07000381c01301a00c203a003090807a4218180540c101c400100b00500612403460340c4e82001000c4c1c00ca42e0141e4405031500004044100e84a881620305980780c1c3c440751410401c0ca600c0410080d04503007011280d4040c1008040f071241c0d18801c0c00e0300110701c0348502503030324685460b16482890b4070105200c480d62005a000001907004038203a603028031800e410f60307229911070400c2c500c0c0003040c2c00040b400d4064003a01180060400e5201d03810f85d00181c413440f0101000c000c3c3c5404404406909108101085c0003070701c014900b0201480980030001c00302d401a40c80700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 228800728 1250 228799478 228799511
    0x322031704080c0c0402040b0409050c0714031b010203040210030c0c060207080315180105131b0914030c01090e040609050d02030405010e0406050303090103050903160302030c06220f0501 82
    0x5070740c141c2d0000d1020404245005040001d1000140c05640030740c101031078450440c034280254003c1d550115200c60000c0d00c1c002c0c02e14243c44100303410801d24018001c401000545030340c000c0014000100b00c0d02030301c83e00900c05000701c0340900e40c0a0b00c41d00050010b05ca044000b040c0100c070585c02c0000d584140404030307440b800904110350094503902d990b800c06414100d2000d400030384607401076410002c05585015076684031070440da0290350390a0100140c425240c003c1048480b010010b030841414081016800070702103040d140310511103003001440e034080581c0e4800704100d860002c0c41c0a0310601000c5115071125030001c2c854007002c52020748a036101d50400341141d1040340141c0c0007290810056074044801a82010155000c0113890700305404291280b10b0404c7e524141030304c80d030100da0b20000c00c00445415810300401c0821a0260f454002e440380c1c00014062000d110713440110301c01004443c0d0404003009180f04105400806907903070088008105130170b60346556102c00c0f450340381100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 228801978 1250 228800728 228800731
    0x9210a0311160302010203031b040f03050105060f01180303030e0114160f230c07230a0f15120f110c010c02011406011d0a06080f07030203220317 64
    0x20386030007498201c030204252508500d50041c80062200c00c40400260b40c001c0101c075000705002c0301c940e410b000b82040703031001813140d544030100c2c02c004540f0000c00e000c011b6001f07078050300c0c08841c3d0a1228261030011100c040302d41c0c040c08001c0100503010400240030341c8c00340c2d000e5400c420022500c01b0700c0040851170603c08452144070030000b0a060543c90740c0c0003226140341056400c0c1306c841c564082130644045500050070590049000484501084d0108558002070240c08100e00100140e10300e00c069040d04001c04600826005401054800400070b0190959500002c18009000340e1102119072014a41c1840c211030780e9078007003952001c05c0e03008088098158028503a81c80c0d9401101900f11402014200f0869140c0341540c01000c10349404a0341042c401d103000380e6991141c840680310024404072180d070141006030002401c5421410081c81172507800c00c801c120f03a40b410801c4e000d0f13201c00c03a82c0108440d80f007480440c0b60011541c561403014024a8a030068195007410000705410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 228803228 1250 228801978 228801983
    0x1030f020c2b0203070b070c200307080a050a1707060c0801060806040902180c1c0903030b030d0918090501050405010b0307080c0906091b0a120c031109210a 69
    0x2010607009142250392400c42d034404071504803400707048900000e45034001c5810007015030102c0380c040340c0302c14807032018140d1040c2c20440c51440125003c9024004003003000c64203009000e429000150020007040c600095600030000e040c2c0010f05035200b404000c3c0b10040705509150500182c400b00d05a03110307058040760079172110f684035418600003514000c0001c107180d00c11824102c072400183c50300d840300215020440c40540040d12903840745c075082d00446508401d81c0d00e10001010500006070041d81c01d00d4020384080006c2c000000c24141c5038040020584042005242c04000140a1a034040b070700120701c5500180011742651a142540e9058405444680d1106848084c41c5410311041d0011b160035002410303070030040780200306032510017080648030700000d50015a010b071080717540070106041030075015901c0352152000740643e00a119141c4c100361901c198840e0b003074001e104490102040e190410300f0030244030b0820150a15048240c1e0412515190f03100c040f24003001108441071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 228804478 1250 228803228 228803233
    0x17090a120809070b16020904031407060b10050403050303070804150e0c010e030105011508040206130b1b030915130513060e0c1801080a140f090613150b01030f020c 72
    0x1050405540f80071460340015105810820030915510002c00c00b1010190741903ea00021b5991810180ca2a24115074451001c5400042080402209a102c0f1a441c1c0c1e04807192125a801d00d013085031107000d030740801852980204049911207015514196200b4800c4030982c641c14403000030041594403a076000c030300741c0d404046000030540e001400c0b10012034054000700115803418030b050700040d0200070880d0901909602203019034842c58100d90385600540044202c040d500c18644005500c0580600c3e83c000c1c1e10030603c03250000103c100e81036510010903019800d1086642c01c1040d0f4018100369100c13800780701d0002056151140300c0110f054010000203205880c10300202510324008000500c45070041040c540307211210406c0c5404c4800078a0100450b0b5034070058030300102035a03a08641c1e01243e400801c244182010a01442801d080c420355440d911040d41070042c0701c000d00c600424410b000010302e0300d00821980907015480051401280e40507091001e0f0003264441c180b40030701e0744c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 228805728 1250 228804478 228804481
    0x810060b131e0306020a120f090b0604020a050403052b05030708010b031e070e0109120b0414070b0c0604140f1f02040b07060f05071704060c170f06030607020304030317090a1208 78
    0x1512500c1040230310050f141c8148020b201983d501da000c980000d0185228560204507400d0243c414426100074551002c107c49032000c3c824214011040ca82c141c0c1d51810408400700120244904140d81c0032b242e8548492603540d0801d04130890941005000f0b2503041340c40c41000100900510b1058040c183c2a222006240d10510004041681d00e4000c258840301a00e4140c0009460040081d0b006402c00c007905501c540e09d000840c1085115072100071208008924540460008100b06004070b11030081c5820001001c240d06d911412114107181040d0444449200e0300e0298410090035040a141d0062030310351202428202034009101c1901c902d1b581d941607420750740041c401c003034004029003002d00d05024a2181c403810380c00d00420041c20641c649400040e821301400c07002e6070150341400d80f14500d00d03006801c181e4603501191018802c6c032409007c1744000c1d0000c4115820f60b80c040c0d03980f100c1402c0c68031441c0c8401401604030b29162051504c0b01d40414800500031011403100d9491000c0e5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 228806978 1250 228805728 228805757
    0xd1509050606061305040f0e06100e060f010503070f09080a03020a0b0708090304090f090f080d0f0c05090d11031603110a050a0303030e0a08040810060b131e0306020a 73
    0x3844001012039001d60410401d40c000c00c40300080c02c8080705c50844001c2a0340e0034034401503002c3e00702542e80442038411941802003039aa24403489007601d0304c0460b002e29541d1a1004c210350140107140d1640840c1081000c90540c1c0d1140d14062070342c0c4400e080144003251340d00d20051402c0e580801c280c006030414411030f0100300b038044209411103080d14200d5520f00304030b45070a40301d01c103500c1034249059650703c0c040240810f0380c02075450190494500c41c95001c40d420004402c1c0d200d1003d43d0186d61901c41444050050391103001408c4030310760398807030402c0180130038028031038400702041c1e40d80b109840818039980c2d4100445200c441ca001440c140c20752171032074002c080d282d2148070180705211801050203180c881c03e8440c0c04590301450080303a441c81100d4198141120201c0c060000100020045a2020001f5214114103c0103200708111035603850181032038040c52401080010325103008000544600480d0540e51200301d20341004980c0e00d9480300201da22144e1800b02141d00148a10603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 228808228 1250 228806978 228806983
    0x71110022503030207060503090708030a110d030606020c13021603030b0a090509060705070303150f1706040f0f021305240d240618020409240e04020d150905 69
    0x210300342851100d007007003410366401a488910ba0b000c0c0c4020460007200144035070200300a01401030002c0420740740d84051150b40240182c218045c0494a0b00c1790031448440c0c3c40c0320f840780c4002c86a9981c06418180c403220b040103490805510882c17090750b02405156150805401c40741036061081d240016800b201c0e5090103403000c0c582d40000c0307101e40340c0400c110b0f20800109290307920094903d00b55a0300e0034580b4040d00142680c0c800781c2480b080701c03440418000400d58034103090703a050030160900390700c000351240d40e110300407580101194a64885880000c91003862a2403040c4007c2c842c4103030008202030380c811580200c440b40103012070200a0448000c1014100708442016101c2e200c80203840e444503803102c80b121070310403501d282ca030030f84105008440e8402006803103e942d040c010502c0040d4440003940260180c080400d182030100b510448249418406414040380c20b400301c245001580343d081a40280140e8000000b5040c000000d1200031040c500030039100d0f800101040213050261 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 228809478 1250 228808228 228808273
    0x21b03121815040e220614040312110702120f0a030504030605060423040c2112050c0a030e04060b030a140115020312040c030b040503030a0b040c050403020607111002 73
    0x358086401c010a01810000520300c0c2d0344408005085c600340002c841a0b9003021070a03482c040c0c2083c0c40c000c8810080440406601c1c060f5000b941c07040c070030340004041c2904503010032074071a4046500f0002c1e04014207003002d018640c8905e00c01540c0e0000003846a40e42040e16902c005c9000400c0000c05100300b00c4584a4182c001038241c1e003c008070b09004507200e100c0101c000c1d82190070350078440018208118100c9182c090105d140c1d6841201d160001590010000c2090407541000d000061200e12407251060b10900004100100290401514180ca40030700d1140002c7c1c1007600c4200100300a0041e2009500800c410f401c006528030710001c011041c1207060704440301c501908010b41c108e199002007030b41c0e8000034190f1000b8498913146041840d412490380001d1108030b404003003100303102002c0041e61040200240c1030055040d0300c010001150000040e060101e9001d21017800907050000290540030301c2221f10051000d0068002400e4464041000c5d0040e8421400b564950f1801d00009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 228810728 1250 228809478 228809509
    0x204082e0615021c0804060f1d0132070c110307030c090c020606090c090102012a0206010b0306010f03020309030d060b0301050a060801050a050f1f0305070e0907021b031218 76
    0x10400000c04d400107240d45800b501c090300b03182d02d0300e10255980349568004c0d03030090840e00901d011031144004641c045c00c41000d46003070368060303507500d540031004440b441080380d5a0302081100b181c1d201d040c241c99985d00d020083d100c041c44500d580981d40c5080144002031070284000b00740c454602214401521600c2c810f01003190840d001380203013a100c0fa54000e070019444032801c0d803a0221940100c1c01003817801c1d80305001d09100c401240e20724030100c0e807140380c102a560940d0341c240e0721050f4058180c0300c00d40d80140041c102c040c4000109100c2d174013039500140f548090724035268540c000c5a0070350b8800d4002c4c9155040020040140d80f40102c134101c014400d0b41004a400d41c1b40c0b10004202194601c2800e00581008001401c15901c41d017a403002c2c03003104400d4400b003003002d043c0200180822a80e100118000201e40d6601e403034020020b61044400741c0c020151000c4031190545000e41aa4510f83c0501c9816058402c0f0011400900034889030707650f007480780d090950100030f04160341e060305 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 228811978 1250 228810728 228810763
    0x8010608033001062006011d010b16031b080d050711071208033303010f05060906100905060708130911190512090a11040204082e061502 60
    0x42c010038016200e5503411121107080408042c00c1d80c0c0418041441c007800c02000c103005078400030920440308800050b80c1400110b8980729aa01e546041c02184264807500841c2040d0741c520200081c403c03a5202281100c4800c01c0d028030b040360b520380301c0756003040742025802c036210000c002d11307140d1141075072002079030090003401e2082c603001e00f11070002d404440c0a4142040000010504203014111441e80ca85c09500a10024a001030005180c8461a5103620950038084405903900c03c0380241405490010040c001070b4484900700901c92011200d50030900454420008050352010090300032540184a1140c1d61500210141d1072544550011058145000c0c0019100ba00c00300c1a0b175070404201100400d0b1141d411002d88650103102101191400c1940421401041c00305000c2c1103079100d214090350390140d180400007a40514021a0300540c0301080c1030120201c0100d003903a0b81ea01c2144c003881541c50407107500c02928400e40003050450710660505951030790401c084503030074061184 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 228813228 1250 228811978 228812047
    0xb01030510050a052b0c030606090c05120a110a170c03070801061103041211030105132402090d0f031209080d020a020123060a09050615130801060803 66
    0x9112460f5034050640500300008103034000d501c0041d240c014252003100288181126481c3c64104400c49003c01c84040b41020b1002400007460b0041ca01849201d498a1b802d04070314500e10805034800a00000e001900caa06506003481c0c01ca008100803002542c2d00300c21200140304082001b807014090034220541002081041c45c1e00601050646100d40780041c41003ca00040c517146001b40e410410102c44c1180201d0200421040614000001a0024005039491035641a0190b41414019201040070803a00d4400f00400c401c0e00c0c0000103180c001428500d0880c007041e80e00060000c12036441d290706001105054019000c43c01251020405014107801541d4a040034040c06142c00e083c9600400d094035014001e4108111903560548041c141d1070103017040031a842c4054400780e00a228840010910340400d003d440c1c07083c400a840c500b81e4207141c080ea150b0540c054500140c41c01c007101e5004c10642001c0c06640f004002c18402981c80e101d00944403085401007408070800480b100c034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 228814478 1250 228813228 228813239
    0xf080703020f040c020a050f0303010f06030507090e061512010302010912050d0e0d060203070f09060908030f0304030e03030a020c130b010e0904080d111806160b040c0902030405010b01030510 84
    0x2582d801400140c0380816120101c403001d078070700108040000c1c1180070b648030000101d0740c0003001d98101c600005066122990742e51040d02100c90135114080007071001c4078140000c01c10350212640001002d00942c030703100544440450075402060000050800ca03100400566a02211a00c0a01201015022042c4003aa101d980d0380301c211010600b40403446d070801c025a551140c20300f0701103401080655503494140b074010403240703901c20250003203950241301040c001c0c401c0400a042d9040ba200442c91301c52000341240d802e810051045007000021580c0c0c40847e1018005031005080c81e4000b841104007040401c07000081b42c40c0c80c0170556142801c0c024060381d02c840c02c068401c00598105499448034148100300784102440c071010316040c070450011401521000340080c0d602c855803d800c10501d10700700040341c843d04c606144401d07884803c000c0403807203150405403c42d114050012416a81d103038000b00343d8104031003d413007695442c0061041943c040c010b040d40815604400c1c84043e0402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 228815728 1250 228814478 228814489
    0x9010509010b04030b090304030803070c060606140d05150a080303070f1e050702040908190806090c2506090602091201092607061505190503100e0a02190f08070302 72
    0x10b200c0548a0905d883c0840c0407440d0a0080758055604120465030f00e15040d1809885451407500c2140c003549003640000b440b5226403002e00c02d001c804d540d26482d110701c0915200152002038041c2c0600100080251070741e64491010b00010300340e40f006562039250086010380700315040144681070001d098500b25060100841100d0307500294105580c40c0e40d001d0002c14010145540300404445000845c51310780810810554410085030b61441d119a840c2014064107800540e41c28008007000e216212100030102007128111880c40f0a9540c0703800d081e04c40c00140e411080090f601c1e660300252a68290130000b9201c40e075600864000d2004005640d40c0041e141c40c4030344244e00b070080d4030442690324880c240031124a9030b08140c0511a0201f104005010401c0911419100c1c075840a14004201c0702c0100300021907400a01a0010034810b24240740500103000840721036018912170040182da81960200304400e180000011080c00d10140302000c80c49900034101075404440104016640c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 228816978 1250 228815728 228815737
    0x3030405030904050712050c0c0f03090a12050a05031206011d011e0e03070e0601020105070801060906201b0f010201020909060f0a0b0a02010c02010c0e06070320070b0909010509010b 80
    0x150f80000c0c5507580c3c00000c440f0309090007008000c1d90305150a0000c101005005015009048401d42d0342c3c0c0e425001c0000c2c1e172481500c9859803c03014192080003006280328a83c0c9080740a201910041486aa0f9842c21580b140154556840880c003e00440c0d5a0041c60340c0346d40300940e1031411008024400103041c0c858241c0101200d0302490032003c404a100e1210060b150030003030120f03240d4a880b903904481661044035038900641c6080300003a01d40b842030420f54125215500c440904904081c0211a10300041c24401740050502e082e4007403060040200400032a1181c4190200500300c200700078908a40e000f00078110782c010700c000200755840c0f50505811035000c0b607880e100c4005c1400480c0011629620800c402007020451045854040d00000403400c4a036000b00200384034500181c0d40c0070a0810a5a04907100384030200c0040d0140d01007642d0604840e05202450020760091032070012160051601410003244089071803c1515030280501005c803810354440d0f04090000003507018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 228818228 1250 228816978 228816997
    0x905010206180139030203011a0706020f03072012090d05010906020f21040c09050604060302033003010806160504030203101a031b24030106200303040503 68
    0x911186075021030003580a0003180307032025525400c04c000e00b102c5201404900101c83e401d59140c182503481c4511910840c0d047c0c2d004c8031003030000c400c2441c1662005800541007240d078103600300501041c813450000914070500c20303651200107007146d4420b01c17009802e0041d00016541d02400d0501004404141a100420000d540c039007030f80c0d011400e005014008001c405000e062001880d482c0400c900710040180c0075a052804003001803440c0008002c910454001d0208030720400180282042e5400458021100900100b092616a00042d00382441e01654800810050405410590803076952180f80c508405010341190f240080d0103440310801480e8100f80d07081070034510074442c00765054401841d00078089070400942c414100f001018040e40c01151424202ca607280036140000e48004a00c1c9546c4e612686041c130001448828074201e004454403403407200b20041810440c2014600a000e55076039000b000040340d0300c0d01030100340c4484800d0150820801c00010800c000103c90082c072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 228819478 1250 228818228 228818251
    0x604090c050f0f090108131e0807060f0e1204080c0f15040603021b0f1f0603020d05010504060c09080c060307031d0714011d1203041203020601060f0905010206 70
    0x81030180200c6081c07044412039550b140c00402c2c009008295400603101131003080e2502101c988a12548000d0840da2400003001d0f91154600c0070340d2000041c2c021840c0c7d81c46800900c1c107120082d0340d4030094648a24200303074442d68500c004150100f0402c200d611a2000c05061440e060030a074032951205d0a190800c0d016019600c2411510385403100220725071110401e00301d84964840f00000c0c040e41c0581701600e0154804c2806001c1d00e0004540c90040ba0303245130050016050103003d03100010f01e841500380c4070594541307000002d0307118a08040f0809204130000601450580f905404540f5035011721000c00001e5842072141010000701510b04401c05c8901c03d80320369130440110f000c0c1070002001000700c0007104030340b442c05400040b5541a1140080725048007090700e801110800d890b0840451200114135400c0031609000c0300c5100c0b03501da100103907440d0a840b0b003144404640ca81400f14010307440f08004106196012a840300000000d290079481d484c50900003c1d80e070440034184a0201 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 228820728 1250 228819478 228819491
    0xa020702091503121305092d0a020910020309041505091506090a030f0201090b181203040302100c0b0702011e051305070621180803040c181b030b060409 67
    0x359010480310301d03454400030059035650184002e0b54400c8441341b090f03901911042011030501c12110f85030b40301802100d038800d0410b105a4502c800044c9025001c2c08120740c0c05c11060419031940c5082a113900a1900190760b600c42c0e15040c407044583c030000407251402214400e10403952064030b003640003054648106500300036200028490300c54000706603404081c3c08000000c10144a02c41c08142d4002d8840300c842c543c1d60380b080502c42c1f10705400a5000414803004c4201e9282103030102c200d0301c94603412281007584950104100d01c1c6507408050100b11051111410003a60302d80c1c1c0c0d53322852510003030001180740e10840d00080d0081c20688040c90f29031000074500c1398400d08030b11055401c101205c0d2450741e03414010b80710195006141c0703001a50189505010382d05405030a111f94111580d404c1c2c225101d4444c038009400181003240da40c1d01c103c0e0b001a0800100c4c00d07004843c1c1d04642d0009190b9000840203c441c0c0a060000d400c1c5070a10310081a6075403600700761002c0700c00405020500303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 228821978 1250 228820728 228820771
    0xc040606050a0530010816060806100c140c100f020a02042a080702010b03011107061e020304030f1101181113090503090f01020613060c090b0705150a02070209 70
    0x40c614200c08001425001084e00024070440250b0504803050300c030581d0950034040c41000740350141c41c0242d03804190120042049800d100b550465468118074107010344903565034030b8204030002000314a41942c4981038001d0340749010a541716072010b07141803a605440940b072010b03441ced425013040a4841da40c2c9114000c036a244019a905083c9428a01803186d02549030028040441c2540c0004c01903280c81d180d00b10034181482014401c807900200c15040042d95034800c4040c2c0201300f441d603030b4511041c050b0709902d54a40080d6008900c01c0d10b800d00c1c0010119001861403140c4410a035090381014242d142404542092812603a00250790007006441e01d000702d441003002c4080407989500d04041c3c2420300038003102138444d03080101c56403094a215000126074503282942d030b00303055101601a034000a0b000c0d50000710b92407170f1303810043c11149c0d607032155200e16004000c00391107075001840941031b91144003103c81c0d44681544011410280b03143c0205000d0500207085c00c3d240070241441410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 228823228 1250 228821978 228822007
    0xd020405040507080411030a0809060f070506180d080c0904200406030506090a110a0c11130c090812040b09210d030f0209092202041a030c040606050a05 67
    0x6088090802c0c4950f042c0000001c0440c2d004440984020300180080b940c0380ca00400d00303403c02508441040c0c140070f01c02c030070400d595006094600400c5020404040003850a00815204484e00f1601809058480c030042e410542ca20241004000a80003041480c1001a0540e114204280c600041c07a0002016280c00c0410b543c26480d6222008100000c400f64940c01051103213405031540300040c0c60344841801039030052204005201400d015115044d4800d0105200142c0103c0da21048890300c00c0c080b446501070342842d0160692035141000070740b03401c0100680242207040c0104407112800c0f010b4900740c0594000d6200d600000280351103d940c50f28400c408159041100c151100d441c00b003950384d14034007062000d01003170405824521f081468425a8541c00029040c5a200c0e0307030701901c103188043c8018205034180403480c90540583c4076407117880c2440c020f44198074017401800301018038100c8100300d844e22840c00c001040c0001c81c1d008040d5035401d0842c1c24141e882d1540c0b490800d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 228824478 1250 228823228 228823237
    0x120a06151d070309240b0303130e1f0e040b07020c0303040605070516080304030b010e2a121501030b0f0a0303110703051f0c0309050d0503090a0c0f060215010810020d02 74
    0x10f2103001d00c03c003101035035601c60000d60501c440440040086c4000581450f0300c81c007510216006c400101d42d01000850b07004103296a00c411500da00d13050a403810a044650700c482030b001a4200c81c4503004010402c280d0315012900320703c5900092030b1010102c40041d9591142e07018000030000c021407008200102000b0750031a80c510040c440544545402d0560f039a03400c5480140d41d0082c4c610000100e1540024180d03001e03112100300d08201c800c040ca00440c80c440000d0240c000c0e104200500c0c0020100000100d005070307010640d0b038a5003044880010140c0300607081e00c44c40744550b42c003141c565940e400589011070764541481250201c40000150402d01250700c058854080c8440c454410040d466030144039072480c0d11704201a440040e8102c0485030000d0000301b20344d00118005480390300890245a01600503401c59401042941d06c0c040740300300e03650007a0348038160b600e424000c0c56010311640b2210110101340a86a41c540301c40140c0d1410406500103119a00040c0312410036000c0d0100c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 228825728 1250 228824478 228824483
    0x150c05071712040602121809040b010e1b030a051f03080a080f060f040e030d0e100501090b013005152b02060f09120a06151d070309 58
    0x340d5945036201c0c241003000401c48074884050141c0c401e2002500094800c1c2d03400c2e00d840307074028041e0204000440b40a0782c081d4902500000401000203015031305e0b91407407441a4414a1240425454254007400107000a490440b0361510102c00c580d140c142681a00d41c4100c2c502004101601d9280b0409002c02c08554000c00550580c034000c000d200201004148902866440c10b81642c1c804001c000d10300410784210f9030180202d942018140f900da086412110801405d407850b0145ea2500101200d2410282959640045900c000041001d02c5100e00501c1c509105101c500c10300d6000a02c807804080e07910707015002d0b004410000105011006004101e0303e0002c03c02030402b07039014112001d00750246441b039000c040318000319458842200c543d0552110034526038840a41c20041c541e000801a0750286406219002d116541c0106181c101c8012304c0c040c0142403501e080010907211000a816001a000340007005082c1504d07a15000d2401c9030b40d88203c0507100d459086000d040e512102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 228826978 1250 228825728 228825733
    0x2030106271104170c090a0c180303090506160b0a0603050c03120406030b030c03030a03090210090b07030c0f06050a051009060e0c030709120308040c0b13150c05 71
    0x10a036401030300001450701481d0900225184032903040c007000c2c0d44545007080c03010300c000d1000304a82c2d40908010308403a09034030191281d450f05640407800da0402180c02e40721440c0c9030382e41a07150380d4000c040d00c031003400c002100d80f403030754190344014000d502e40d40302e85406840c00003144a0518081924510a00e900036105001410a45001809040ca03404251060b0140801c0b2080e6840c0004088054815030092036040030301d0448103900070100020b01503094050365038008219a402e0008091111468400141d07408441c01445011011803200320144103490505019100070071041c0d40701250705140c604055036403032a140c030040700200c00c010070040c2042d09010741d00c100c50300164441c42d1251581000e8560310400d6000f6116144101c60140b03d540c3c0c00b1606810042e00210350000c0c00d0b0600c005034627a6001905503641400f90103900103030b605020301080000590059004101e141030b041e01306042541070b88010456486991491101c1b030220303089a501841e808001d26401071309 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 228828228 1250 228826978 228826991
    0x3040f15020f1201080c090705090a03050708070609120f02090403030f0f050105100c0804090515060c010b090114100309021315080c0307030b070507020406170309040b01110a0206070c03020301 85
    0x2c490b40281c00c00d104480415400600126202c2c200044140115100408643c903a440390001580c855200184194000c0c002c080c01101180042060400400502c0028011140340c068000c117202d5250300282e45c0100c840326240c003c94010305280c01c8007a01216503011300e85a80c907098000301409403132104690300b0301c2521403a488656020a04072801034460100c10b9124038821918829024001003200d40b041c0010b12401c1015804561700003041c51100c001c0e40341c81c00000b034182d04105032512580c2c0d1078180080c45400c08007001401010b446070b402241407109400030b20301c44583c0320f44004269a0350780386020b6581d1401c00140c04100c01004100f10350385609100c0240e5240e01a48040307110724006c2c04582e0a001401108581d041000c1d813080d61035508045400b83e03c007a100380da1050f1259000720355251510240741c00003d001c3e0045541d46c03050018841500d514440301030502850f1641ba9994510102d01010748660480d0f0942d500c404601d0420b0854105800c040d405618054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 228829478 1250 228828228 228828247
    0x90e040f050c010806010c080313020402030f040302210307030f1104080f01050609090303130f051009021003051611070e01080619060303020723120d0f030b0603040f1502 75
    0x403409112038024015540e01c03960306001034400304026681c01c2d00054503604004041840302001d5a00104d45178503c08160443d500002c09a8106484078003842203440107202c10580c04010710b240140d203103440001c0032051440071150700d01009202c18281a101c05184918482e00e52188503841c10f103054903501c0e2a20703040199915045207915120542c40c000115285240100829100d100d0a40096241d5542e42d1150894601900c40c100e0323003155422101c100081d400c1c441e94182c0d012001380011081810b00401a100282c8002da1050505d840f00348100807161910611445d2000d050100c1d01c413503522600303031a02c00c0c19440084049042e100110b040e810100e80030380501054501c0c42d00c2000c008a6120490f840c912000300941c2c040030303041100c0c00000d1013030060340143c25443c003101802d00b00441c6012940540e6803515401c45002400c4441c2c1000d15035145410500d010000c940c903810200d0068800176002820004840c2c540000b0015543d0080345aa881c1407820b545500609 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 228830728 1250 228829478 228829493
    0x118120c0f050601080f28030512160e09040b01030b0c041a0a0323060f04061203020f060a140c0f0f0c0f12070213050408040b040b03100609150f090e04 67
    0x2c0c040c012050103185411804010700203250308007d071551140d07000d8180941c5c0c4003103c00003164000c0f030a00c40180b0810303841c11280400f0500c030b41e41c44840c50703004092400c070003000c124a07041c0062140b02c04005100105494507105410740790710030000240e54858000c240f2547c080c40e40108142076400c855081c0308004000542002d0045880c1848040c807120b101108245108400c030f00040500400070b0b9441c5000f03042c003841401c024000040558440f401640510942c840c268090780c06a50b0610040000300115039001d505a00c04002e82a0108500a080c50001d41303085587d03007000c1885500008581c04450300020005500c60780c4040d505245070700e6050308811101c2e1802840030b403080d50b144040072680010b03801001c00c5a003119641451005040180003075500b12400e00000c100340e2a8140104003914084144079264901850300d000442c1441d0011010001209410480704558840081c06404c5074200300b29458005401210050302507800865000382c954144005d12218 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 228831978 1250 228830728 228830731
    0x60b03030f070b010518070305070c0c030807120e061204140a0f0b01081209090709050a0f090f0c02031e1908060103050708100522050a060e090118120c0f0506 70
    0xe080c040a96aa80e44c00700541b4001c0c001c05203001000d000e000074520b5100341d01ca541c1c41085814076104804140e02d03003803592211a00102c07a031402c00250602400f184280345240c0e022a480c1042d049079003030300030500c6d034018202945500415580400e0410441c0003100724031400c1082150301040450030000d400c0d0218681c19241c03102d98800214082e0000308500f8251000344850300c1c03a0404040074802413040c020500e5081001c081008545656420304d07000003050460700701c0c452142880030050498003244599140e030703850060482c00b4640c0102c2912102d031000320400e00d103250003c0052109105010007174400051815041c9e9020f500300301d056005040c00e9030204a10b5503260000da030552000e5640d240c0e41082c1200c20005880c2001c8005000d101c15001110074080003100031003910300540d020080b0f584c46142c24004141a1845590722003480c030001d106c0090071000901000010303110150175600c600300005405401100400001c0d54820780c0112a20070a04080ba02ca960 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 228833228 1250 228831978 228831983
    0x4050309010909110301060e0120030912030903070b07030c0506070801170a03080c03090a051b0f0a1a0304020a05091501030608070e19060e0108010e0d050322060b03030f07 76
    0xd860801103a1807503188906161344280c4c4001d0b07171840c0d00701001a00e0382c002e02d5240a041094251825201e001c1804108401001d074100841d01e03002c5100400544540a80c2ca401c100e0b80700703100a6840d540c1c0060903500300c03040100344550391406400c00320b60149030548094031601c200401c0c0726a40354440a002c4c100c2d103840e40b0284402c45030020705616001d00507005000104400b02156481809500450b04064000b04035841040599a20390604464146031551060f561403034041c41d05043c0c1d00d21420360300851700480c80c11300b0540e020603c3c0e104200700c501d0f25100400060b04645400c410080035200040814010745031101d00f58401c500154449400203040c001c00240c40c807000a00d14054130300b810341240c290303901c10b0307903d8800b001428650100a61181030000340a144034100c1406442d00b180046812128450582c0c80d05c100072858800b04002041040311039250141ca8000d00a0240762417040b5a07030310700304030016082d6540b50303d0385400000340407010302484030001c151951 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 228834478 1250 228833228 228833237
    0xf0d02030a170c030a0c03021b010501030c06090803040b0307120f0c18060207050d05010219050706152d0803040603020c300d0e06070507050115030c120302030d050405030901 77
    0x24001502c0b2011a042d03034403a40d001001d20110b15062210b8201e5404124940341c01030400c1c02d00300701c49104541d582804144e41e59100014010b004405009038098425401e06d440c3e120f1518084943d43d00c12840707842c03c99400440443c20140c800c0a4004030242d01713071400c1c03100d8402c6210017001460203000d1500422621503c0e250360064a450001c00c5420390f4000c0c00e15646000244041c80c1070b6140200c6095600f000810400300300103203900980420390780c4990b290060b604d40001201c0c6256100505500242e004004000080e03041c1d10807000c1da101c1a603046d0310a80780c18081c8002540280211340400701e404a9102d40c564040e06010200708115018030703c2c503040724950b0000403030bc80e80700c10300d244032910481c1007000700510620411000005458004074001c078248102036907028000f90000810304181b01090251988440114804d44070091840e0f5038000240554820f0355100c000510010080c9802401900c81c60440d4034000d002c0391900c0c0c0b51154036a400b0340c0e600d60204 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 228835728 1250 228834478 228834497
    0x71a0708060f09071b05030c030a080f010e0414010e0d050a0f03060b0307050c120301080c101d091b03010306060515180411090d060606021e06040b090f0d02030a 71
    0x30718001ca00b40c60201405001050292580102141c0104040256a14a0501d0003214001074001c2004092843d02c02002d1a15000c201c1e5008000b0306002c0c1004020103259070040c4401c44115010580260344044203500344040e444d80c06000d840c076882d101009010b07030f014603484c40303401c000207040381c0c440c590740c0c1d40d46c0010607103044e0100e90320390003441c0003d981070000550540c096802884110200c40403112000750700c152010340f03a48260042c1006400240ca001c5a07800d0100d0915412115410005200c414280c0208029801c030f4000034440d1800c04003045a041c50620905960741182603450380d2581c580c20400301508262003803d0007241c16552014a105c21101601c050943c11a00e054100c2285000c00c400b4020000044c80d80c032404011404180c2d46010300e4020440c822403010594500d003047c06030402207400707041c403140c0c42e000d15900c0405102068050748140d10010301d420759100e0005203454031400700c211003510310451441040c5c0c50380000240c40300020030782e61090725 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 228836978 1250 228835728 228835741
    0x20060405010603024207050d02010f050a060e0610110f3d1e1805010e070b0d0203090111030c03090d0c0210030209040b090c1803010c081605071a0708 66
    0x8401e00c1341c0c05981e81da4540341d03501000700d0350389480b028014840e040e1803c242c6c880c0c8826080c142101c642c0070241c6e65521415084101c1c1d4020968480b0850074104001454800100321026000348502d114001854082c00b0f1180292800515800480c08a8500c0c030350302c1003016621034000328602d05c04140112046c6036443c0700c816840c0c1150b4200101c030800d03503c05a110028020000250345424424020301500344200e01c03030820441131400000e44002000c0c20400d0846440c0c46044105410101007030281c81c0300344e02120800c0c0c00c0c100e40103070740b0355422000328010009001005a44c01c8000203111b02c0f580d461010354001c103012015a038000c00d01480c08d4400011101e0025008200c100e54604d015010f0360281007030744005040801c010b40e24100240c040031040702c031040110808601c020100c1e0080c1502d00180e101940200150000c1e03410160104030700800306a60540c0b400c140d004181e20070004d5690807680b086c0002c0c034183d03c040c070140303900c203084030880c00260000000900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 228838228 1250 228836978 228837019
    0x405040e06060a030206160501021603030b0d021509031c020a050d020703052a131e06030b010504090f080d020405040509191e1401020301030b1e0105012006040501060302 75
    0x280e02c004100f09081440c541c207000c1181c01120594404010b6a130340724003c1442030008140043d00c01103080403170809864054221041a80c031103024038030806100d8011385405892000716001c0c4e00d1400e8072182600c0c002450f100c4802802102c1c10a0110076104c0150006046180b10344a1001c0d540a03503041c4000302c0c1d42326010b1102411590240c02019281c281581c41a00c441d4850070710748088034110408240060740300220b0b001095500c0600200c14110174980c01046050f0300c10512610f861030711914442c4106002d0944070b0303691540c1c032804104540005c69812603010040d640c4602444000742c009410612030300d80194240030000748140e50101d00d581c01080c22030030301d02c3c001074207448641c0302049810721071040841e20502540810b044101442074940500000343c3e4940c114a0155040c0c0b030082c050150204000c0040c6040eaa000c0c0100c0307055801c02c0c604100a06419003000340d01c004584c00400c200d0061000b80000c3c0b08046d040740096030700981c0d5040c0040061100c072507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 228839478 1250 228838228 228838231
    0x2a0a0b07050304090b04020912060406050106030b0108061915090503210a0c0309080f0f0709061d090703020915011106130303050402120616111b0108100b03010b0405040e06 76
    0x206181c1081100f8040c00c41305500c040c44e50000a0001428040c21402045484103420340e1031800b6446602008100319540c043c141c05011706260034804070701d114002034101d0b071002c1c100c14860340714444040414114501c428006000f0300c2088050700b0b640d6003020b044040c5c1401054028010810400c10a000700114100000c655004440c030b001c2c80c120b011520340d400024110104400c000001800c120104101c40c800c0c8642e0000d00114a07509040618080c4594001e4003403a0600c0810031034030780d0b0108441c03125602034202d680c860b9540b40b000e50520086c0d400c001d45c041a298148464042d6600700c4003000c0200f0f8a07410811a103503210300c1e81d281c10844032019016a20405076000034882d4001541040c4007503c41d201c40c440061403507061035002c0310002c50000e0003940c448945940f081800e04003d104201400d0032008003405a6801032600264605100c111008260300305000e80c0d80200a01601c0060394595171100d030103000a038001d02ca0302e0701c51403d281322498005000f1030500d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 228840728 1250 228839478 228839483
    0xc05040302040e0709020c010e06011410051803011d061506040b0715090516060503090604061a0d0303020c010c080114010f0507060c0905150a02060601030e2a0a0b07 73
    0x9050510390760801010341000c060401c0c06016600c0c00141e000644e0015183c06203501c1d001003600b562604d085850807905030b12154000007801708011a64413003d0020b5060070035880e01564440c0005e50b884450700f121441e00d43c01d90719140c0184c2008504403450000c00941c9400d0f1121921944002200d40c000d0802c41544440f08020811100d1800750003400041e10901181c4c0045101c01000001c640745e558041c1c1301a00140b072301200b20120109100d005c0c0415040081c00c500b01602040d9079400c008000030265a542c0385e200c0115541032003a1480810f00805412144045150003000b83d0003a100b1001c0560030242c80d40c08442c010607040e07050b100806040780941d0511001101c098204510317180030701100300261808660f4034021040540b103151102c65155241c4010304c0b10705550082104c8491070b050051803841580400c01942104091801140e0740103801c902905001c03892000b003002c502e04809030a0010300310103601c0c408030b070129030011402d980d560003021588101c0000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 228841978 1250 228840728 228840737
    0x1416031803051605090a0e07090209130204030f0209070815060306010c02030d030f0612020f060d02161103070603110d1d0a05060a050a11070f080909070509031b010c1118010f0f090c 80
    0x1841609d0f042c0d03020300304509000385a602d0400d00610508100da00130381055610b01c0c60000604e0960a0100d8041c4d000a0b00c1d19010b03060b8505203480210032080e01c01c480f4070552000001ca26140c0c81620b9802c2c00540007821b13911526845038001d130040c00d02480003074406080080002d110401405491001c2d50041c2411164031401001c008896000414813208a40e09006080314041d0080e80c9000c141d124841211003541010b04040c58500103074000007c040c1882c2c40c0090040c411020b5904802c0542000309420b40340f00910012a40d524024240d20300c0760001e071000740000064083d001d074180c107108000f19128000303200c05580c3d0019203021559002c00800c07001030f1080f0410340e886402400018181030002001500d0900180c2d900000a0070128000c201c078641070102c00c101c01c100a115a01490302100040c114001144014044880640d504121134803840d00726480f1620744540300c042ca603150074501e0030351041c80c01005000300e50b0b000702169411081c0318510350340010303884 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 228843228 1250 228841978 228841993
    0x1050a1803120609020301030503220b0f0a0e190e150d0b0702030906070309060f080609070e130603030320040609170a051b011416031803051605090a0e 67
    0x2401d844800c2e501ca100039032641e03160b00c0025908007034809940031303600c201c0280d680c1d0b5078504541c50702030001400811121000000411034404004215221981c0ca9075109450b42000e680a80350302c841e121883d43c00c60b0440c4240076111140c40c03007020980383c001c0000401610360340e00180c075481c0c0258086811099101c02c150102e00c0340d98055502c4249407040381d02e0f010294001c0742032030708000011400306445003400d0108c0358010341652048410b4bc0b0300400c05282c4000050388040c40908000180701c40c0318070351000c80c1c8412040b980e0b102c00c408010311a4941d02d2030024020498141d440005d050b03070703580b142c008403000c4013204c2c2140c3d01d681d29600224200340350080101c8100608214521450100e000011000e00c024108003104040c0c1a44051490300050891004090b032201254410002604020740b0084143c080b1a010f14103c50b907034a108007060031a641680001d0702522415843c1881600c0100005081d5641500c2c06001521000c002d00e007074404034020038490b9000702c04c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 228844478 1250 228843228 228843233
    0x1506050420121017011401120f0b0a0b04090809100c1115040e1609060e0a1206180b040201030c2d09230f030601181104170a02010201050a18 62
    0x41800d60008601120b0789441951140302c40c4044560680900e41a5142d524144801040700d039058010300030720300c0723480d02c001c1301781e46480307070541822002450a4200400320f10341702d03429800800140c2c0041c01c03c00c60303821281410529a080460303800e00c04d60fa00e41c2ea04169034030400600c260241d102c001c4000300701082c4104081c4150a111b9450783c2e680c1400f001075806043c266003805031290a40c0c2d2003001c1c0c050703e030007031440105400c25014400c81d041d0051540e112616038008549900071041c0300d21100f40b82c0400a07050010403403100d000a611030905000c5ca094a03035024a2007601c0c20090984c45440c252800d855050701d00b182520404070806803000d40e087d0150900304a071070b0803000c06484090301060b02e08055800b13107800d4040466072455051075290450b45590849c000d0030950b1608220001030240c021212044580316200314000010784d809039005094810b15500648071490300d0b40341e441100042c1a8010740c00e03d000718410303405034403d2051440103075080c08a402c0c09034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 228845728 1250 228844478 228844507
    0xd0e1305090102070609061b1803030806121c020c01080412031e05010f0806010b031b0a020c0402041d0612060c0f09040e0307030f050c0307060b04091506050420 71
    0x14003100d942d540130005580000c070340d4400e200040e4451100002d03070103d5280300010b02c0c408034841d41c050101e007411201d130704114095000102d0307a040c9084c5da44c50340ca0b40085180364000505603815031150a1001035a040c103462140c2c03210345140e0840d84006000401111665025240030b815070144160b0840310b58421303001640c503140c02000b01c42e05a61500841c004880090b84900150714411400b402600e01c02c2c080c880c010001a005107045090070140d1942541e8041d071044a00e03000011507121080c000d00c0041580c8030028400c5403540d546101c075000c030320b0742810b5070540c000d03040000800c1032030702d0007002d00740038420002001550360350340030407050707a100782d032031440d9110305002e451010390b0b480c080d071143d03403103014041c0d80c50ba410703813030003a000601d2500d5400c07e01c00140f140f0368150800006803049070383c204402041035000c1c80f000c94001d04d154080585110003440400d1600101c541050080319816101003040c2c08e90f0180c800c03028038264042203020282040a56a0000503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 228846978 1250 228845728 228845731
    0xa0f231c020909041401180210031d07090c081f050105130503100c020c010c030c0f020109090f05060109080c0303030a05060f060313060f0e1c020106080f0f0d0e1305 73
    0x8268014a4402c1440c00181c640c0070444003140c12040a090400d54164207015a00d021019540c8280e107044441d03002030040d00039107440004160760348a500d00080b1001000300d8a0903490010703130720641c2e280d205083c090040241d5000100300c104d0b01140c0300b11220240c2e0a40d08422400142080782050011a15603100f090360078064406900041a82d55050007500384244041e0400210094020006404c00020320941814025110f40f0000800d0b00300590120383c640c0b09039943d0180d40b0310310051780d4804054021280661a0819140c04a60198000c60043c6000d803290044c0300d95802c249540d035442040a260190414000700707490494540141d60450001040481c11165501c04105c1c540c004a804040c080140c0381c600045c01001d10030520f28074800c0c4007d11080101004050743d441036040c50755840c1c611080c0349042d9510039440000035084200c140c070802541d001e1940d46d1144080311040d001d002e0307036840004190003019050219480034003040440c4291040c4480200350 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 228848228 1250 228846978 228847027
    0x40c0c0201122a0302031009090213020c03191d040c17250c0c1406030106180503060915010803030105090414071d040506150f040c03110a0f23 63
    0x700541240f07103410300c0001c048002c4850f54006889181000040c00c09600d59402642e117145408a0b000c0503858032540d40d288a003040d000076a81d01c402504040c5903210b0001d240e03454000d10203181000075840707480800864401040032016281310310402048419030307a00c03203010420b0601020002420203c800350b00c11902c60080d83c605040c0380035800b1b010000041c1c0b80c006006c40f0040000c20401c0c0590074081e044040540f07002201c00c4001c5000f5120602840d810f0100c2c10b07103d440c1d110307401d9400902400c4e0140540c0c503a4141300500035503e078254002002820800c0002107848070000007924100e4100a003003103407039192030311070024003401001e45a800e8045c0e008042040c60098020a00700c41c141c0c280c0450503d41424420b0400c100988181e41c4c141c0c00f41e40c480050f99400c085100d4035402140d000031080841c10b001c0e001040420131402c88064045200d600950f006030010004900648034514040024550141d50701c40e06180781e06031010510441c1c41c2e01101040300c002044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 228849478 1250 228848228 228848261
    0x10e03060117070b070c171c05070807200f0d0c03020f0102070801060b091c050607050d02120109020703030509120708030a0b1306030201030f060608010b09060702120a02040c0c020112 81
    0x762521300c00504c65122410644580030205003c21041100d00040c070040c0d15110041e00d54524070b002010216100c44c0000341c2000008180d9100b842402c03021900c52940c03102c500502001502c40500c0001801e80000c1e2281c0608001491740c1d0404074035003144250b020340d1030a583c505680c00c207c3c810080490300c504501c160032001c91010b409108400203411628900c68440d403131310040120958144003007030402104801080001103000a0140c0c010419040c0141c499040d9180c0c10002d008252102079805108000060103460302d030300810709035000350b60901296455000c029035078801c425410507401003c110100c04612190051504038181d04c8010030030040010000b400c4010300c0203041c3c51030f9039030f00f401c0007107681602ca07074030390100041000d125907803422001400043c0c0501c141d143e217403000103408990340d0350903040b150680c2d801840035441d9200e0380e40460782c0d4034811a0480c0100d01d8030b5400c60301d40d401000b10340c4105234160360f02c9450301890301443e4082d1031074000d0400c001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 228850728 1250 228849478 228849493
    0xa020705031615060303022e0606091d040f03050307020109020a140a0806060303090105070204111204150204030b06010c0c2705100b04031e080d0614010e03060117 72
    0x38105000602c0d002403040380400500c001c6040521103074141c0b0024a600c64500740c000c200098011030042000c0e1100c55076400303034140d52209000c14005803105005070354a003000c081201504044a0800c0c0c0c0c1d030000b03041140380e240d01113440c1c00f404c060314041c00c00c100504202001900c54001154006094330020030a044241d0205d843c06503150031682d07a02c1580c103141e0b030319801c00c0c0d07402000801c0520002c1500d802c1a2002c2510fa200ea410b00604005000400c1c40a6481d6600911894101495841d45c0d0310080101600460b02c107460031619001d4115982003880a103000b03483c1074036045a68030b0b2031921440e00541d80b080700c0c00c10440b40c086121400080c0004424035810381c5040b403815900e840c40c800544802203580080001e03105400c03010080c031510f0258426101a00c0c2e00a108084004140042c841c1d40802c1d030070001c100b2040020290041802da40184c0e003116030308061401805c1c101e10041d5895410045c96a4165000c03000421451745441c1c2c1c6020000c2107101541d214 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 228851978 1250 228850728 228850733
    0x19050c09041103010518060601020606010912060207080d09031404050102030f0c0a2a081f150803040803120a05070c1502090409060b100801080d050d0b030d0201050a0c0c020a0b030a0207 82
    0x30340394225030420a030488606041b00e0307980180140c5921110074806048140fa1643c00a05044014090f402403900b1041c40e590803c1550340c1203421309500300b29a03640315000188100042d1102c5281100010003001c00c8810641d0b58509072011303200140c003d90300b07140c501c24030300c000f03904039000314842442000080b401242074040c1182501702119400c403041441c035915a5149641a4030a4032554048542c040c2c0002ca1004c1d085107a00e44540013040c6420071241604552405c2c0c2c100a20705d000002e000070300e00a0000050030030011810389000700341c1d41ca90f50081242d40450f49800410b044115803400602c1c000e00448119130307401401801c18042c040030030200d85038020304a960035a41c1c4102d1441c0c0c0740428176101519224508011503604143c04c8944805100101100384040415454000101c5030030030111800054110f0700c9060b06050000e01911040c0d038914016441c10443c1c2250a00c02c90990b00c3c0c054028000480c410b180090b980b01c2a48001c2401c81c1c001c2d0b0078040c0900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 228853228 1250 228851978 228851981
    0x1060e0919360c0f0b041701060f080703150e060402130609020d020705150108031206030c0607061d1605060d0b04060e0a0e0307120f140a030e19050c0904110301 71
    0x8091001240d04030704441c1902d00f9078508209500000704480f100720080000b20400b504031403d40380310020701503a807181d5181c11805040d094110380c07504030403004003203250040040c0d01c0003224010b002440e10341510b81500002c6511403405c071005034200a00150150610b0302103180813209000700083e80607982c072803100898005c0c4810a0115400190070002e1140070408042050f0b000038803c1510352409419550340d00c10343c8050840c440c0c035000010017554060122408003100581a10b50b2180300346450801441c04c1c1d1600c1088446a00c40712a01e1000000c09811070f0703c842110001541c100b1041203150382085600d0121951500504040341d1900e0103440018046c040d10100e55092902000080d28014100809241d20500070278000c54684801c1c690301c0d00043c200400ca8981421040307a01b1810000041e082c4100020b03000c22950f81640114058000c40068035030604102e50b420303045a4000c84050302c2079006203c58209446c000130299001407143c940c200e900f544aa010a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 228854478 1250 228853228 228853301
    0xf070207080105180106080d2a050105040819030c08070309140102070c0e16050f0705030d0908031e09030d0b030708071d13020306160509041401060e0919 68
    0x3120075030321904034940209028010240c04104d020780322402208c04010080700c00200a041c160b41c12503024400784204c00c9490040580180c028000d6141a00b0105519840111102d10801710f070001e003070301c81d48207200e065901d8800b5610046a0f4a815000328050b1202c568181c0d0f0310b42d0354000d03450f160f46c401d01c018400c540c402c0c03e60208192400c1c0305603070303803d10042007000340e55103092062105952000454400303011082540307481c2c42c10360070302c60310b540545d2444000407458441c041c000e2109440c05103201d2600c1d40804503040100c4c0e043d284026a00f43e03039202456000384400d01c005603080d004048100c0019046481030f80d0748014846c603180352a032041c030790428400c90381c1e00811006038155612554121480802d4150789c1c0c046a074412000305600d40d01c0c40700c9840c260b00c40388114112030f14164020310a003d482148614039040110a10a6030301240c1079140301181c84c1413144225114070201c4056140415041440c0c001038100c1d294800c01d101c00d02000e44501421040c07140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 228855728 1250 228854478 228854491
    0xc0302012a0b07030c0503071202070c080d0306080d05090607020d0204091e061503030c0303050a02040b040e1017070e060613030305130506090d081b0601030506090607030b01080f070207080105 85
    0x100003400c00e07031005000c0b00d5284605c441044010410456804d0b040b072142c0c5140e202c100350040c1da9030641e00301640148016003103c203150042e190f0700818a64141c1020341540e110714299100c9400d00340080c0e40d94401c07000d0158202006001881c058a0f1404450285c24005000401c102d02940e444055003040c10030f9003110484070011103400c1c80140e115000750f410078200b40050141c1180c9015001c400720705802400c0644134000128100d4480d01a05e0051038019901c5440303e27200c00c40c60051031012901a5040c6410240010f2003000010018006655000207010228101054007483c007074000c210680142040000165000d5407000e6200118000c0e41d445480d003110140340c0700c01c009154409031090000f4410515035503101440381e01d07040e0f8400c0c05255500c2681c40100b48403115064007040e180916070002090040100e4014414140602514807a9495880035402c4480500c8201c1c00a9070710000220102c01003130b40740d500b0030708500480380c41995a0403d5800d450045414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 228856978 1250 228855728 228855743
    0x609170f0c07050d08040315060513090b0a0c080f070c150902100c0b0a020c0705030d0302070c0f0b0a05071401091b06021b010309080d02070602070c0506070c0302012a 74
    0x2116048010300000000e000c0480d03041d000c0341c0744c548800545010f5404003802c0e05044910b000c1c14a03d090740501c0c01400c1c060700114203501907880d02c0008060b00042a60311005103000182d03904030610666a2a222984480c120b0751103072014480c004074010020742c14010013102c0040400c1c0c541031619800394003014042040002c40c070500000c0038030759460f8001e10141c43c0850002070344e0140c10039400b1000c81e0005031640180e02040d072400c4507607817015130107002d0300c1801c60560781d2503002800c0709030180c9c120180c91030380c0d102122140341552140390110002844643d250794411001030075014003c0e003040c00006414240e86013101c021a074211303000400808440035040c1c1004160005000c503002602d0640a842d000700b0304100c00030340d458105a0b403030f10b90000708030b4880180c80c1048640001152145203619101c002548000307420703118030707001c0d0b14005207a14102040315030841e131140d05072030654616030054518400307840c0704000c9071004030919244001032070014030102c1c0c007074520f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 228858228 1250 228856978 228856987
    0x1b100203043c0308280f0605060307050717280908010209030303060d0318030302060f01050f0f0409020604080a060b130209031207020a090606050324030a0609170f 72
    0x10300c003100c0c0288403684440c04101c0c2c0782d803450044044440c50b00c2d090305800c000180c2c0c0c2c0ca064101e100030200000c00c1c01042e0b110f200004d0f1002d05a070184088030700520b41000a59240e104200250004070f51000009400300031940020f40104000d9400e040b500c00c1c000d00b440451405c828031241c10086074010140310401d00015150712403502d00041010100840c074020080f001701c0d40720f2000402a6000e00c0082c0d112a082610827140400000410b8030b18081603526490029156001a156040d20121401c000300d000d04e8090625006a0130042151031071000d0740b001c1c00090b01e070004060b41e0080e02840000740d011703c14091010349a10803000003035011092410015480000c0d47e01000d4076106100e1111507844c002009012807010028854440c0380510010b072111415401000712a030401c040040d940782c100b0f028500610140b1402400c07040c00c00010444481c407041c0781c43e0316034486240c0074003040307042e8404c040b0b280c014290543c3c0180e500c020035202c0d500040c0300c0e50803200c0018 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 228859478 1250 228858228 228858263
    0x9080f03040305071a24032103090f06071d0d0c0b040602010525121506030e06070c20030703080a09170607020601030b06010e15031f0b1b10020304 65
    0x3071701e5118030650110005002e0422469100d8003802e0b91420014041c1c0081c10005290303000c02c6160f1460070f1040607090407544c0c0850503211508180d45d506030500c181c80001905072004504240300b4592503542104504200306039148058104c4144c03074004c4500001c0c1c50110b52103070400c1c0050480485515507803480c2c0302000307003107074002400010401101010410f00b0705074144200d1855000b86007601b840d6003102c220b04004c0c8014205000c0412004100040ca180c140d001810091903d2090b1002a0b0360b40106071019006074400500d40d0585000d145100c809203a580704000307a001d0100c8d1038042e200d81e00c203040c5503c038080b03060101c1c04100c001c0007003040390344c0103c42100c5c1d01c90103030550f8140310102a5031240c0c10301009145000388030014603ea449071084000342c9030010452040d02180d1146000300b03904c2500e00c10031406422800b007411105030020003088400d59005a03107028030a84082911026040082d074650080940d024501d06050000e1030280340100406005810b800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 228860728 1250 228859478 228859493
    0x61804140a0e0f03090307050111030409230c090a0915050409211715120307140607180b0705150c0d18030e0f120d0305040219081009080f0304030507 66
    0x100765945840c4c3c0200444a11510702185d400d00301d41d003e0801e2014034041404413411400341d0380002814500d0400724406903020082418800580040100b015441e501a000301c40d02c00e00b40c030f0b60780100b0500f01c20400c00d0480e900007680200c903e10565800b9403039000050a4403103401c3c0a944d140c401da8030012a0004034181503080c3c1c00301c2d0600c507411800b202d0313022410307400080c070501c83c10880344103c154544410380d204c1c0c0ba01f1180003e0b603030f80e81041e14080060b1880001501c5952045d200052401c60003540b280c058403243c1001503901502d0040d02002e550b0040f0001c841502882011624280da102201400780140b54801c070303268402503d00f1001c071400e50010220940780391210030040780d0040815060080203461220138042400086001d50003d0380050043c3d124000ca000440355055100500491088800c00035422903042e404814940c18021a1240d4104840c0384281003000da010b805024401d1074aa41045d4051800020941080340d05070041000000d00c85c041280c1c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 228861978 1250 228860728 228860743
    0x10e0d060203060a0b090d0605070c061b1709071403010906060e070212120a0b0a0308040f03061a1c03110616020f01062d050a090617030306061804140a0e 68
    0x30b4400c1103051140b04000105108105000038208c81c2d070762404140e04a00c980e082c07030895a0018020b101d55060540c0d0024030f503614000d9900041d4a00564016000d034031000b140c0a110303000000d04001d03040c4541c4032069070850000780e9040d0f50361104100090701034000c07000280032808080c5540d240074400642403070000b0701c0d6554a00c108100000c030f41041c0450705600428000c00000392038880c103001c9000c64440d500003603c210004280000c44a558040f44800d4a00c00c200510a0815181c0e1604034071030045031465009001000500000904019000e011030003407808030345015090f1072050800350199200050711410906801d00a40c04204006607422400c00030000b44c0c1c03030a03480700405800c0300c4038102e40007600e0444042d100803a01c0d200001e800b0041079a14103e541e0081c0f00c009100c0351088240c85a603515403140940c5000c015070740716079009003c55141c642840090516a0180c031aa03c5e4003075650001109450701c52000f00340310303055490000540ca480c0b140644d140c0090f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 228863228 1250 228861978 228861989
    0x2709130203150601050702090c0901030b0a030f03080c0403060204080c040b0d0c1a04030606090507030b060f0d150b030405100e1605060a110a031e0e180402010e0d060203060a 77
    0x1090004900140c800054045641c94042680c0245407510001222140700d0000b01030741c072504a03818041481e0303000009200c0301d03100740c03002c2141484100070320410006901c0064003412084100d20701003405503500c83d9101c170700800b400d441c258403551100300300e03046030b0807100e110303404400c1c01140c5051038455140001011640d9844080c5256210803400308540603156071002244451542000071000b41c1e0f02441e170005062100b80c0e20b0b0701080c2c0041030112a0003002900b06403c1c0301c12800c12030221203049110388d405500e090b94042ca42c038080c124a00340c0904041c0c807664000360201181025500440c822000b5104500084800e842502e000c1e81c00c1c200a6004492407040c110100500002102c074280c803040c2d2141d0650a090f0344d04581d0103a4498140204042c1c00200341c0c1c00b00c1008044901c09550100301d003c621801c44040c10003198a80c0c004c0040900d9000d4010000c0071594403e10501d002c106250010000c14040d1403003241c203d4000b5000f1007441010310f00f5170002c1d8042c25 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 228864478 1250 228863228 228863251
    0x41404051503030d0b030c210709060308030117070b0a08040212010b0a0306050405030c0601081c091203032a200105061008070309080703050c0613050d050f2709 71
    0x10040070002e612440b034a01009200303a0380b11807001c000d4409205824940500404030304044840f010f003903590708001400020309000e482c0c2c001c20f07440458400e507420713603800804440c1184c0c04d042c10080203038514a250310403446031000006803810040300500102c061562442e0340c03801c0601c1030000030a12900201242e90620504120703640305ea0b803120080b0303030300407001242c2501d0380c5c2005810341c230031000340070100e004410000c0380c10344000401c410028564104602d4440501400302e54002d1640940c0b2071070b000400310640400e100340c00054280720444900340d10b000110342141e44085880c881c0c8000300e10107100d100d6104011038540b294451f0960001e12541c541480064040805104444203002400c0c0100700400d100b58050091070b40c0c485003d943d601960308005d04241c001100c8600d840c03040400140032001032000c10b04213154084001d01c6079a003054001d8070503420401c00d00c01c90036414013400c0380c50880c1e0090b5800000800028130361206141c4280a94084e0082865400301c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 228865728 1250 228864478 228864511
    0x60204170c03010606080c0702010c050a08091e0f0907031b080108070b09061209190b0a05010909051c27090606020a0b060907030902060703090807060c0203120a0c0804140405 77
    0x50303410032106c640c0300f010110565540d03000e520041e5141c0f00081800f030560300c102e0340c06c4010018010018070310300000316260362454502c0014401280c0c4000c0d02e25401c0100500c044416040a80d0010f40001007802c01096032081200e41c540074440b44042d140c00149001c00400004074148a228042c06546407514079009520f40400c0703040c4a00c05182d8002480c0400040c240002400580300c191640c0320190100000c0781455005842c040e1181c0709810f107022300005003032840e48180b041c15580800a0020010000500c2e921103042c0310129050111038111414003c4000c644814000ba401d1100046581400001c100300c40c145d410510956116510030004102047d0115034000d00071584004280d841c480c0880140c592040d009412a1000c180c250400d508032142100f0f030f80300901210211680c54200312501d041c0700b400690560404664020340c0441c80b001400b003403400c2d06000d8110800799031200402da0069010790b4511b200c1c010074082c54034190241c9608892000104480c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 228866978 1250 228865728 228865739
    0x409172a01020f04120204110304050105040209060d02010e04050a15032402031b07050109021008090f03180603090c0a0b03090c0109060f05070c030b0a0c2003030106140403060204170c030106 84
    0x59114034001d119130005d402011380f0071551144c011010b9603002840d40754890429140c00c40c0a000260f808a1180840340001000d50500010341c3d04c604ea01656455840380d03203542800003e00c4082c2880081645a680e0b0102e07801842c00700da07000f103100f44c51070681011038219004640060007100040341d030041051103910700c8010f4141d50300d1807003402401c2d6103d1642c60020700410741407000a4000f075001c200c0c90b80c55900100900d2003400d850060342e09071559044555120320600050300480328540e009003619003402000b440d802144282240c182071005000100c0c09030f0103900c06031401500108015038800103000e540510780081c01d000624034240580500200c03502021101080008aa85c60a0142004080008507044100505039060112035a0040c0c546502c40102141725200002030a00c4111a10b0004030030381c202450860342000c0c011501c116840092a401c10414080400412030620040c0300400c0c40d5000c12652030100321801c1c1c2408403100400d442a454010200103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 228868228 1250 228866978 228867007
    0x120e1c020d02090705120f150a080d050906040902030c07050706021216030210090503041706060d0f0302070b0a12141b030703110c0c01030b1c020409172a0102 70
    0x781d056044800080550b903014003101e2600880e200f000c020030b565414804007481d401c2c2410b0180510440c110100d11140f01402250441d52162005d81e42c420100401003511460140c9400e42005040170314065070380c0780c03074010303a041941c0b0002c40601c0001c00c0750070480300701301da00018541070018020540300c520024805021383d0110070001c242107490901014800d02600d000007208210811100d40c1d80c0c00c010741d881e006800354130085511039004144024002407a00d1183d40c0080c0100651400340c1d4a8241d6120556012010740c810128040303a110b07080c074058003a452107680c60034004481e07810a941078400c50701d50b903546421180140318401c59840c1056100d01100000f865607900c604208500501203c801080314010128106482060101d01445c0d00b00091703806220700c1d005c45003040714410201d1206010f500312019000c0050030300c1c0d00090340079800741152142c803000e0040c00310b802e5800182c415598004180e80b8040e2940712040309091081e0400086017040c0b032107000080e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 228869478 1250 228868228 228868249
    0x3062106021c050412020d210b010c021e040f060b0a0c03020f070303020601080f010b06120718120b241e0d0803010602010c02010b01090e1003120e1c02 67
    0x14a49500007500b211100001a100c5001a1010b0381c10401071400e03041070740f8100d1039484014010b00510080000c490b105241c68084100c00043c09400002241c0b0030000803d192104903052200302c64071000075a0b41c2e510241c00d003480340a0a55030364401c1004200032101c0001075404403500c0e001092104501800c241ca40a04040c1458001a0000c0c10140d24003100540311007031f5841307500c0d000300c101580815410304a40300740044601c00039401e026217003031381c00958285400c03180620590008031100d00340d0305c1c1c1007911030404140342c0c91280c043e2056594260011207a0036040380c01d08080000b180788007640451a080c0d035100d407840036210f40c1440c0d18921030440c880c00078442040e86210741802d1900d620302005100c94848003691030304080b10b0b0000d00c10b18001d5441c144019220034010b008800c01120142e660303d01e0380742000440f0620700800b5090440004040c000400050318020f552150440141c50710005111004100302103030b00680741d20280300c007240149c40c00603102c507034080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 228870728 1250 228869478 228869483
    0x50f010515040e070b302206060f09090b061801140102030d18020315010501050a080a0e0a060204090b06120412020312130317070e0603101701020a030621 68
    0x451034020080025190a196401501031400d002520080c1003c290301300400c0c1d15406c0c008501031410007801881401401c45411184000710891803098681168020110921982d0f00181050300c0c0d2803604280b507607641007115025680ca000c1014007071000d066560209080382c4800c1ea000700d4180b48040a90188075402d82030580340341c0360880f0380c02031041d2000209824002c1101c03c0c0c01806403480e00c000f1030001e078040c0c001e2107451003030070540a1480e4103a0750107031151460074603100d00885034404001c040c1000155140fa030300c450740806200c0c00b0a068040c42c000b40e03d45040c40c002d6001c680d490085507208820400c0340e60303511640c0040d16580b01d500a4444c00780c00c40b05410503400c5205008001d006010320308200303c02044100180f502803402541c4a100f117040301d400250314070034281d031030b00f0201d0124032201c41d840c600b21000315807251541580f00c4102e07a461584c06941d503001c8c0704000141c2d4001c1035205445500d84108002007031201c0c0392840c94840180d1210204d0300c0400302 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 228871978 1250 228870728 228870731
    0x1c050601021f02121003020a05150304030e0d0b09100c03090f0215070b090a030f1b0b070e060d020306090a06050d03080a02120108030a0201050a150e060d0519050f01051504 76
    0x10070441d031150f5054035101c0c1d0035903c41c4070b00751514070740354550180d81d400101e204503042c0001040c2c609105100d1401030300406445880c507200c82d1016188452410001948041107202d00340c0000d01c1642c0841c0100070714002000030302d05081c401c00c02d6408101c1803908140c50108074170041403d16800c2424160160b400ba001c0310070007003824030213101c1c010010745034103d101c041c030141040014a51132114026525034160404104044541071a40c00d01801d2603102c503901c440100b03042a02464100e05941031050441c1c0702c0710302041083d08242d14001d0404e601104000003410a020496403001c803200e4101701c102d05210018000f801c546e803010341008034100000d01007901d43e50460f1511424a410902c1c95a51610441c0e41c9030300429070395006500b0000407410700c1c0d100d0b00601020b0000240385060741400c00a0060400d6001040c20380d00081050800b4003141040c8881031404007035508a01e50074445082892609810340c01c281e0481e0f1408040000840060b1010211103070700303e80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 228873228 1250 228871978 228872023
    0x60a0e09070e01080a0c090209060403062c01091112150c0d090c3201031109040510080d090e0c09041401140109090b060708160506010303051c05060102 67
    0x3446440c169240d000354400002c41400807400c1c0c9070020308101d006204100300c00b402034450211000f0ba0042c020040e401140a0100b0300014540c1d420920f101610741142000324804c221108612940268004000781d654802100c207104001c030340452003d006491504a000702102100e41da1320400081407031050342c0c2c4003c140405180011078031181c5a0400621480c852400c1201503440b080c0b04a8400480004000c21000d4a138130795400300c01c01c040965822143c08400641c042d00300d1f00082d26403113600304109002a59584612409912400940551b15051201142c40c140a44150b14140034007c0000c01408403600e00d21036000707480c0c1140307588908005001c90701070003c99140e170411003047c1c00007044015201e00d00090443d0240c1c3c424060719030703548000d4102d03110801000d801c1032041101801281d0380300002c20744240b001c036500e0b4065025494040c00e054080e042100002c00000c1c15045141e560440e1824a46000303104101500f0402e0003c1c4d0f0380d08101000d004070264580 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 228874478 1250 228873228 228873241
    0x201060e04032703060515031c0305091005010b03060307080f03071b080d1e05070308040206090105070b070804050c091e04050f01020a05030603151009020f040f150e0108060a0e 78
    0xf07100f00d01d9040e982c03600c940903075164034056018000484415041201d0151102c041d4a00066050510078200c2d0300740186a10b05401203003d440c004107400c0301c4d8801d1881c0b000204929100d140e00800300c40d07490f9622401c10104050402c00d9070f61016000303a101c980850400c0c58084102e40109034030825413041541c0310383c107041e81c600d600da1001c3d00c1130080350840c452080e0800b5806e01701c28034030703582c0e4802c05030341c64404c3c2c40c280039004029002a070b071100018014105080103000c000300504005042429607511844000000c440300c03c001401103040c0700030484104032011380700c10120780c801c6407854008036041c17203150103040a0340001c0036a0081410700005102d810039006100c4000c1d507480350006d1000c2c19035402503500e94040d108401701010704464894007103002c0c50404c2a00d401c0f092030710340c40c00702a4111480482107207a00b000001615a03070b0011500090100366010402040ba1500240c52281594480c905001c2d03d0410040c260b90b03441035403425224004084c5500d82c0b101e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 228875728 1250 228874478 228874517
    0x5011508010e0406110a030c030605060307050a140405060f1210050904030503040201030f05270a03140a021606030c110a03051c020702090702060f100f0504020c0a05011505100201060e0403 83
    0x1c0140e901c400d02d001820919281d4503230441c58101a080e103080c42000d07507401c01e04c041c902c4100d1740b4400261061164174100c0e441010080c0781c007080b8180c0d143c1081d841c0c0d00020a0755000c1d40410710100d00000b0112040b0400640c400c0c1e20415079001000000e107000c000c82c10071107000300000c04009001000800f168000da000445410150000308a80d26101051a624146259602001191440e103060200100080e500356082d4555074014103c000030740441d000e0b401800980096000c1c21302003d900d03481103060030009181c55a404511a940411f02402000c508900c2808680203005080d0200e5000b47c00c8584003140e00480c4503020f10000c50520082c050454000c0d070003c181d0051101840c1e0004003a8090014042d102296444104014461712298401d0081b50344004204102e07505d0164080c049008514050303a00c172500039652682104c48421031903941d56180d082c180441d041c1701d00645a5a07041e80002c00605040c60b13145000d00c08010001000c002d00c4040383e040a00c0700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 228876978 1250 228875728 228875741
    0x72a09110d150503010b15040909020a03170a081302012111030a1d07030302060c070309031a0405070914040803150a03140d0e010c02011817030d05011508010e0406 72
    0x8801c2004032900088414924003a140319103071081d03080800c008028a0060740742001820700f080c4581c5814030b80000c44020780920710040c3da0112b94000c0000c0411002101600e01e041d010701d0307482d507400080174040c062038006400390613002950aa03940050f40c22605400b082c00c244c2004800541c2844120005444002c0902d6140c110100502c001e81e441c5800100c0c2c80950040b00d05003140102688603528107062001034010b9001c0c00225095aa101d8000c05125000e0704d0064070076610b03070306c0700800512500a003000e1800d044040109000c01800340101428481c4024081a2104a103800c5480760180c40900b05a1001001c40c41c600306800303412035510000b8140c491519a00d080c10b0140802c400000b01442c00744c08001c02c030880c452820a001510161590060410990011592801c2a07042e181c2080e004090224402448243e485030414408005554a80c4c1300300701c542c266281a881003440e00b02c03402c0822219600100481e05442d81c84c030380b8881c59511070401d28040c105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 228878228 1250 228876978 228876997
    0xc030408071104061802130b0f07030813200928050a020d090c0306060b030c041203030b031b01090f050904080c010b0a09051e01032f03030a0302072a0911 68
    0x5d80c80c103031132910040e0750060b180e000c00c03a07a1840703a41940d8030754814840c41501443c0350581c2040007040002030081c2851900b100c4290308481c1180352566661a003840c2207a046083c0075016501240d4074503186840d284c0c03014110a58601012000207805c103910a5070844030070164407840042c0700c8045a5040d21400d01135504244042c0101d0b0900d00c5150207140000d40d9442c0c2030102c0460304210300000c40f8040c0d650b4810f480e2402d89001e000c2e9a42460007c800c8003050384401b00c403e2540d40c1003007861390840e10f00d80710b4188403481e5000541200314036807191210480d110b801700b01c46e50300e480040342c1c400c0c0c102861695500c0351483d07041c01054103030510359215800b80d17404910240c0d40c2e48401d11841c402078800399080145407107580e10443c24070004080c1ca040392441c0c00d101238241a944003503220f4684400a018421b00001e0950300280c52103c00a0360200740c01040c00100c1994855440c42c00600046543c1201c044880420540c01191003840e1241c41290203081d031a02260035090 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 228879478 1250 228878228 228878249
    0x1090f09080912241006020a020603011418070305070f032c0a120c0c050612150d02030f0105160c351b0d030c090e0403030e030c030c060c03040807110406 68
    0x340d400c030340c04128507080d05e0b6005e1107042d906002c06c2e0700307000040032030145400910241c00c50f880d102000203010b00904040c0d4004854004410b000c3c004e80800c42e00aa001d600d000c151450042001030030000080b0412007018104000845010f04d0890500d00f0740052554140124640e411030038605070300c441c0c004000d03520b101e4003141c5003588a03040c007010301d2180bd51244107564440c00c020590183c4800b1004944220011070707540400411200c0c0c810802400403d020318281e00004e0900000c0842100140d4491041010400e0305004005030b003641d9041002c4d402d4625140c0c20005010000e0406507040b01800985d0149215410a003000c04014081390b42d80c1d900801d00d40c00501405175215080c42980f02582c90079000c2e0284100c1140240e640614092034002d030a40100c4007d40158185980c0d1050004006401c0c0002c003044e0b9010070085a85a070b00c01441841c240005003e42000309041c03042c007000500c03060890b40001e40000403003205c2100e0000140040001d94050450344 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 228880728 1250 228879478 228879523
    0x40b060613330e010207060f0f080403090512010f0e01200c07030212030901020f03040b0d1e060303091d010b090f041413110a06020c0907020109020409080301090f09080912 76
    0x2039801151807205001c2a03080d5010b1ba641d0703d405030b41540e0340355010360108201c201c010105500c41e41840758464000e00d0401840755071f60011454002502c034540310280d4440f0500c1510b50068010360356106c3c1480000c2100c44844c4121500010440301c102540b00c0c0001825407d040d41042900003542d00100542100d40704c1489031a03895121b040e507107015029111084d91b40c00c5005c02a20102e500f1140094074000c0300c03040f0f601c000c4c04400164144003078204550003015980d481002c0140d403084d2140403c15041410f0a25a0401c1c18050550005404018020310344550f06480300c0e01c070103990b6890204800e00001707014015005241c134190240b0010841c00c0450a508860b0710f600900028030800e079840140400007200340160009a4845206000d4030306120307240d03c2e0300082c1803000041c4160307240d00041c01d071070922605580b26500480107003d00380307a610136180700c0c8038014001c10010103940c0c3c8007100e6014121600344102807101e1442ea140300e09110084012141035a4580d41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 228881978 1250 228880728 228880829
    0x10030b041104080c0a0510120f18051b060409090501180b0a0b0d0b130519110a05030c01141b011509060f0305121c020d05040b060613 59
    0x550418816103030f8920844032403c019040043c218415608003824140780f41d1034000080d10101c400e4901c01d040240d40e010f9222070000c0a11030702c452100c01e54145910421a03040452801080480000080180e440c1741e1001e0703904c1904450403a62480d04c0030030081400d0800900400341256034840c070f429018010420400c85080440c4100350701a401c000300c981c803109015104000034401844000f6040201b000c81c210000e8095440d44203c003103820075903030341c490b883c4031202c108800c40710703000c40241c103c925241501c1036601400ccc06038020449040614002040c66010602e040c1301d641000880c2203040407441710f000303243c008031030091040880d403042d17000d030252240c070030915410310f0845c010a10b207000e000401c0c100e0741c01a00a07c103024602d1620006035024442030360100e920008800800b80990014003540f503e0210006001d10b003a0510000d01200104002c0c45000d04004080304610400078a1090703403411410520f05410341e80c071001c0c0c25154040d2800740f80e01c403d54064003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 228883228 1250 228881978 228882011
    0x41e0b0d0501061e021509070f140a09020c1f11070f02040b0609060f03100e07021f18030318020a0b04090c020307020105090d15020415090503030a0e10030b04 70
    0x100d0350940da0b8161a200700010281c0c241450103444c4006800070441418099040c1106681003262001035803130b00c3c2d50700d91400c048140c1550105500c019a110144068513203201848014250301000350728103440020314035190500078080321a14134613403074400700900140d4400b800c026043c0d4001c0d551a0007a0900300c5140c1c00d000012481141030205804080c01c002003641e031104009840d4509048141201c035219401c010f0400684200380580041c20141c0e45a525028034080c1d0054075004452201c0003202c21440f01d05624098101102019903030158042c6404007031301480c0016540e00031080445011044800107580090429030204007036108400920481d80e00d0b40c003c0110090350041640c0724001c0d044003a0200d50b007406607203110704208020a0b01944035003244011038009400801c200c0e040b94201032000340c4440802c0e0461030304200d40304054074045006600b800400f0070000c01c50130050040b28010828440705001f218040e401007008054000c0042c410894400207828 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 228884478 1250 228883228 228883231
    0x13060e01061701062c0c0913020a17040c0b0a02031902010e0607020a080f0906070222060f23031009050a020f0d0c0303050313020303030109092303041e0b0d05 70
    0x1149502e00580001d2010100d41c0100d000a0042c05e0450340804000f0a5000d00e07800a010b00d1541d181001042c1c400e03592505003400798040710400684440203d00020006030004204c0801c0509000511003c590f10024040c115000d4445040d503800240701c04034114050714a903004691120048030a0075501034001691001c020402c0351251303a5080c00880c0d444454007800341026074200b014088001c07c1c1c0008103a2410044d207614544001940461054440c0390084051042509030b140103d03203290142900034050384103407800d071314107100f180921003000c003054840101c51a001c02185403400e000c02040602c0000c0d00300401c914a0070f101d5110300700d244041303214ec46440380002e0140340c1403c110300000c1e00002e05c68000341c199036054590340c2c005099801800040c10300000103980c2040254080e004406000c20604164a440582194024000b80e0017064241100190103c008107603421541200400450b4001c0c03280d00c80c03c0c1d01c0f5030350040d9140c1311000600325209078564020a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 228885728 1250 228884478 228884519
    0x4151d010306241a0c03070c0503010501050109030b0f040311060a020a090501051603080c090616061404020105030a110d020403141b03030405012601320913060e0106 73
    0x30301c0a1162655642070784a007020709520682e6020005003d50050610000e005400141a2a2a00726103045c0c0d01e1540c3c000400c1143c80c0d4442080902240c1801e0180d01c0c0101800e080c503005840c11961070030310040b0014807025002c1d40c1980000d00341442800041d010300d664000303403040c0781030015401019601521703011010a060080005165100314101c3d5400702401155450a00ca80e9400300c0301d9050182104505460601002505564500040540c044480d00c0154001c00a140020585201c007040041503c44c80c0208400b50740c12004480d40000d1024000a50180c03048414001d40034400980078a6403002c200881000414071550700d0700452403081b05da0500244281070140e2440680207a05a042030100f046154043c00b00d0640300c41d480074180c103014503d05240305094a09900410441c5916515034240c1801c05d0b0001c0180c8014480700c3c80c050107440045200b00e9030180c080311821103940d0003a000d0040c0780e402071704207042e041d00a1200d15074a80706801801c6103800507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 228886978 1250 228885728 228885731
    0x30114180d0903081204030e0402040f0e010e01060519110d11060907061d060d0c050a140408031207120614030d020102030f2206020309030d1a0102060604151d010306 73
    0x4074029805030314100c040380d5000f0700c028a0001032540025480c01d010340110180b01211603480c5195540c0c2c005000901002004901ca052412044000c0e011042c1d10410085c01d0000040c000c082e07010080f1003140c100da100780002c05008500444054040510841042c09044401c00c540c40d44040c0300c07190094039904484c1c854850b815440e8075410b4500c00c170000319803038640441034041c10801186951078020700080c1080700c034019003000c5d120401540000500006041e61901c0e80050841682d080d1a03110542418100500c01e03a0b42d120b000720002c0580d2510001440f0144a00410501ca00c00b420040c4203003a641c052814401c10880c2440d0701c00e005844460000a1052003030360300c240c0744d4003250840c54842e688880420041c038101195007114071012079003c40c40c6400114020081c02004541e9520604643c2d030482d003506042c9006200110b6014102c4e0380e000900381c0d00580211800a2030103562250185991490b5018442c1940c0440d400d65018001050460490740035000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 228888228 1250 228886978 228886993
    0x20c0705040c1b0f060c02060f040605090a02090a0501031703010b04091e180c17030412030c0c0e07030c0903030203120a021e03010510031b0e03070e0906090d03180f0203011418 78
    0x401d0761074030411a2a8001c0424560015001c2f4109802c01c41e00590490140c0c0d95209a940218070607110881c1d0307a50380d4a40794401003080002c40010f01c01c400b0050000d490455060440d0031030984554030450410b2a10341d0f03149035280550000c0562101c1405408200e011100000e14219502d4240281d50781c460031a4001540c18914818041001384840030703600c1d150070110103940d81e05200700281c082041615050000400d20030800c4003074a0a2058888985041c04005064030202d0f84000e0070024400c0c01000040c0e0004280c55a0001880c040039456861071034120003406030b40c0a8043c0152070600c1c9418524210740194141d0744180c81051442200380301c16820f8130244002549030b481441084890a485a0810311207828010255882140c3d05c00d00700801c83c0301511122115000402880b400d034a00700704d10310030003c503400d09110035501111036401401ca440340142100841903441c0045540070350121002501400401ca00f50034001c1c1482c01103114082c03e40c03100c0c80340c0603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 228889478 1250 228888228 228888251
    0x10b0108010e100909060f180b060105040608041101140a030902090a062111040504391a0403020303030907050909060c090f04020702090f0712020c0705040c1b0f06 72
    0xc201441001c0a4007884180c030b242084ca5802000c40390002c0d05d00c241e944106008400c4980502c0e00310a5040e2452022000141011500d44502624403414801d04100802005400c2140940d100f5000a0380130706040a44005880204440080c0700a02a000404143e05034060b48100da00754001d403030070684c0d65074080c1080e00f1075200e40a5a00c8280e11001080b0703250310306e0f000c08130b0507500c40c03840420208100004641560740030740e812103100c50118600e9440601c000d60f0308965440c0c1c501c2082000c9129031291030203124501039070340300e01d080303001003401843c2e264121801143c0c050101c07640c034035150051944615050141714400c1c12103030f0109110a070f00280140c0140b407002c2c0801d14000c80c000c10005114403442c6440c0d081030702800000c01682e90002541d2090100000c1c090756858006002008010246100d100355481480310003421080010000150703031040d1000218507609001c151550055044140c0032101c08140010420195028000c9a141305406c1849a0048071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 228890728 1250 228889478 228889499
    0x12160605040807081f0c051b100c0c03170903040b030405060702070b0f0306060a030b06030a0911120c091806090a0c09050402090a09140a05030309060703181202070b0c010b010801 79
    0x342c074003d0805d4180c00100c000011700354041180c50509040c000d25003071060411b0b0b681d040c01180601c00d150031400c5201450f40b0203010302103d100f0640b410590060f0260350140c100c034000603540340c01c00d58210016a031076004004031070290031080b0b506502c07407401d441c00b140e4a03901191400c00500940c1d02c0090303961a11000e561300f00c1120701e410b40c02d581d41c080c14442c00360403c010010805494030f0b004c04640c0c459000035401341e480c01c01c010602c2c20340b60030854600040785000350300585d407921002010780c0b80403902c02014001200c041041d52200043d01d6044e0045001404c190301880c010300104150012b10a50b145104005109140381c0d181040400c50b04101c030041e402119000010b0038404c4698080d211491085a40b01c4043c12448000e500c0d02c104100304542580c40003040c4036241504004041c0e00001d0327440c080c8200e910110382000ca111030140c00401100c805c62002c11018001e00100010303011030b6044503112409401c08034043c000c0100755601090090b0004141c1560300b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 228891978 1250 228890728 228890743
    0x706050105280e0a111c0c080105030a03080c091f0e19090f0e100603020f030102040305070501140c1b120f03031902070602161e050a021216060504080708 68
    0x2e0000b980083d150500b06480383d20028016164156220500200034522202801140000361400c5102040840d042c0c01111001c405490038800680010417466800103407100341030b81e15240000564868035403088c0d00307000c0e00d5916075014400b260001912584810010314000a0703a0710611013a0001080c84543c0b001e42170009841925044140304211481d08030400d0341140c528000b0300c180b4020012410a031501d25072000144e140d0380100f040d8034211142c42c0000f14120005c42ca042e14541d0b0b00c554034030240c4a184d045c000c0d01d01341c03d41010b01241c00d98100184650958128101640d18034070450a001d100912030b084e074a44205648000141c00420442090015440c40e201d044101c0410980498101c02c0d66400300310f0030340001c4280c0042c05c1851200b080381100c1032a185400c0340701d00d82c2c82c070f41e215043e03001d02550008503000181010085030141c400000c407281010455040460924036128041152500010001d902800500c101d91144041d6002661074075042034440a2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 228893228 1250 228891978 228892039
    0x2030f0414010807030e0a0b2205060a0e030f070303090c0b0d06061b03020703150905010f0f0e120304060f0603050319090f0503070b251407120305071104020409020706050105 77
    0x4007c000a010f400100b03400030021810040c0040c03440c0e28110204a407100c086a00d40c001324240150b0707420398040c00c01070000e024091818812002a211000e020b140c4000c1c1c105911100340006000e80d5400c000054040d410110b90384000d815491809003200c2d20843c8000f0703034541009601020185408c40300a075055010348192861602c800000040078802d0300c20441e0382e4880c1400003a401d10900400716104900851b204042006140c221040e211240f8545c1d0071820010f40788240c01405c5a500a0340500b0015030007011040d010b0041030f491704014139030322001034140140351885683c800c140341070b40c0e21a4101500c03101c260421b0082c41c0f05903078055000501c1406100b400340c0180852510742442441003089400280840a60070041500c011b0304810800d03642407003e100000103050711507000080f030101c0d231350001c20511070700c0005000c003112443d03003034180ea45a804880040190801c20740d1200800d003000c0000300020310526200345000d1040c01000303c4004924601e905 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 228894478 1250 228893228 228893233
    0xc010c0803070f050c0f150708070219210815060a05160609120f031104150c020a09020a180801060b220b070303052202030d0f02030f0414010807030e 66
    0x458109043d591840000d15003814403a0030b20402c0840441000817003071448070400205802502d02494200702140a0202c4082000c1c080030805420f800241140c4040b840191000d0100c5c8a0700304041450300010401030391601c60302041007140c1d0722000c00c42c02821205c8100e4061480d10080003103620440d000308000c00c03402c5c02103004845082d00340002c44c0e400ba80020810100c1ca43d20300280c40c0b880c110303020214242403c1200100ea244c81109500c80400d900540f4084c14501c01d092020013100041302000741400701081151203500890700200300041d4155180c11016901130103100d608280c4100b00c03042c1541c001140c90050140f0b0003116101c03c40d0600d003407240d903202503425001c9504008840100701e800210a951600203191160090341d0000711410301840440d11000060f06001d680c01e00610070402582e80880c04800318000c41c2041c00c1100c4520405074190301404010400c0d03d6004600041c482d00c0032155808602400d0780c603d18550f69100341030f411210b04c50000c0d049035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 228895728 1250 228894478 228894481
    0xb0f0d020901090b0103090c091d030405010c02060c0f060a0203240f0103021b030c0303040312090b07210608070e010b0f03041e02040903110628020906070c0f03050c010c0803 77
    0x524841d413000490b80410b240220300e10000d5100d0001d00c4156034071034120395a0f2240c1c00a000c840ca852680e0030b0311a528090341c40c00c0d2914000130556445000043c0c03150200040c41540e0140c00c00607207004a4030f010959000b4a0101042002904100c480b098001500300c40707a900c061b5650740000340b207240107110705103000c00e00b40110002d400880c082a00d2010081e0f0070f4202c11000c00c05000b180c0c1c00c0b44000c558929061400030401440c200c000e03074001d810100c40400064460741c1c1140e101c1c0d21840c0088141c44c280000000d094101c082107506d880c84c29401090f10702c800319034141580ca540300480041d03680c45055000a21071417061003840403080c00400d001600c2d800c465a442801c00c10410441a05a00014120340c10340f42e007280403c900050700003c03071a00380540355010700a1441c8051011070005421030007201c0f1501d02d03450301e42c006501d80a550748c01050b9084540c0040c20121201c0d142c9407100c1607030040d4041501c0e00e101c1c0012070400d5602c203107007200d41664000d425500b035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 228896978 1250 228895728 228895739
    0x302060c0c03040b0f0304031e0e0f01030b04150306051501020a0303020706090804091a040b03100b12191103010218040c02010902040f0c0806030609062a0301090b0f0d020901 77
    0x554010700041c080710300040000040880122028003082c200e406200d0b980d0341001d10b4080c040301b00c0d061000c5600c5400d225240107440d040384140042c004141c07041e198041280300103c0040098415481d441450800d400181104010041c001d07248542800c00040e203d035080c0001320181c0e440500d0069102d84e9801001920039000740050504c1071b50007080c9413070b165656030880c0d0841c0d00490448e0769107440410590154040720316035400195030400075500c1d008042601d900d202da103100041c9456404640403070f1621446549070405c0c00301a1a0007400340c20305100c0d1342c480f8400544401d0001c4220000a14061084031071800c1650b0706413094414501c14000036200500450055540e41c0750741801684036400b54081400c1c030201d0000301141c88007006000151b020f49441e00940c0903000b04200d0020010b07446801421410981c0c09140b4203c1c000504500c40389a08071100d400032000049501e402e40207410101d604494400c82e4400b11310a01400c4049824007a5200c81600010046c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 228898228 1250 228896978 228897001
    0x31106100e0c2a100c110c1005030c0913020304120210050903091011010c02030d06210809360702160e09010605030304120302120304170f09040c030b120307030206 72
    0xc030500f0303003c2e10420000d441d09003040740e042c0c100382c0b00031410f0f585036581c505000340040d600b028000c485603a010510b1180090503800000c0005111000c0003840b500c550382d6854001b849040086410355591030545040741032091010045005441200390743c000c1400d541c02031500c0740c104000250f0400114504011800e0705c51401e0720184007040303c14242ea6442070080c00c0e1340011540086a0741e000e0041c2c0e200403280558030100a80030300d403401990003103440885c4106036030859803182d1501200c00004241855558460100181c040c070743c6205003600454035a1100c948007680f4500e0342e60114140e07100c0e84503072288118842c0c4c56500740490071044800581001d100000025241c1c0c076680807910f558803e81002d80003140500715081010b034100000c00e01c42c400322104900707500301030b5950718254460780644200c108000c14a02d0a105403101510640d00e001001400003800004019008241c82440303d4051124000c0d800d861480000c1117405490703042d4018542580c40c841240f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 228899478 1250 228898228 228898297
    0xa05180c0d091a0103030f050c030f07051614040501090603050c040e07050d050313050607050d080901111b0705041a040b03030903031201060f090609060507031106100e0c 75
    0x41101c0d40d500d041c42c0491140c4800f038480e41c81958191542d5419424060441030b03e00d841300081240411001c0d1003440e01206869000b0340c02c4d0140e6490b91b10a10f0002d0609500d01d0001c00f103091000400940c2c01106502d072299031030291000c0100e41d032a032807094191000c038000a051903202c08a030941c00d06280d4017a003003900d4488252500540c59400060b900104001d082c1d03034a500200340ca004d04114650000001c0004440131854200507943d000c0d00c030700d02d4002c01001d1248150008134280302c02c0d006400c0c01d11800390180c2d5030740344030b1142d0101c0320b0060368540c0d414070401d240030640d07040078410641d405070302d5110141607160b200c0c10000580000346242c2d405010600003048a62000c0010300307580301515844028940c107103c0002d05450440f01d0b58420443c40200070004030384c02115040a450300e40c030b0f05941e14005403e094401151508080300184580420000c04882601008054840001d014407294807114420111030084203891304002c01801a4585c0e90f04c2c4d11220305 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 228900728 1250 228899478 228899497
    0x90302091005090106022409060112050f0115080c03012702030c03010906020910020c090103060222061d090606160f050105100515120a0b12030f04050a05180c 70
    0x80140769158070110b402c11070203030f02030009a1b20442102c034101d08003064410040304800800c5507145840c60314681e86030418450210310001182404060010600007140301003184002400705001c9003400013403080c0340d88261f1995006503802c0410350316042c041c41e024000100034039801c1411808203080008038051089134544296000151039440c03e000c0e0707071850b42c006c5ca80161560084070511032903181184488003103402045440c1d041d541d6030124941569000180141c940008040502e940c1d0b91100003a0700c170b103011610004d13030f281d030020100c0c4042c150105a104507400c020240302110800341d8150f40d1000040c0070401c02e012075807070b0460305203026800302d1400003900d031905402c48100395124100e03120080b1051004d42040c9201802e030315024200c081c038012454456031441400036100500b0f8a0b210100740d2002e5845250703060410a054090741c1d070f034000c85110044a07912034030509004d000c00e40800215440d0442920100f0300c2c00948000541d0b407120b4104c051503100d104803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 228901978 1250 228900728 228900751
    0x90b0a090f020c0d0f050703051e070b09010609060303120f020f04090c0e0f030607030b01050c1509010c09060c030507150504060221010501090b07061d21030709030209 74
    0x100c03104240100905060365400c0143d46448800c00c0310304044890400c074051119440d160001540e1000890340c40716018642140c0750800c4481e03840700c0307206c444c8401c1040100400d11000740010300c4003144c0a076a0788002045020354a4411106443c1c55100c0035010030b082d002107000030341d0a40c120107124260709a00500d4141481200760743c0d6001600141d0750300e41d54a0309003440b141c000c110007220758801c5511441c00d00060000030713540ca030000e09110400d0740380d4021400e9079008000f910101c0c1d00120039921a10007a204400b208481210001c21540c01d1003040c2c6d1140d4001d800100c10381da00c9644050803000c150710705440c1d6a20007041103404c0c8650000280d00303042e40e44076043c0681c1c49004050780c1c03446201c0008441a81140da0004040e5455004100070303a041040d00089a183d00c3c1d08a4450029040100003080c55074a4080d0701a0b0068038842c02031000b0414040c22402020240c040301035064074604240001c0b0b94181c01700310489008d101501d81b038820030790300042c00f500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 228903228 1250 228901978 228901999
    0x30f0304060b03010606090e1506030a2003070f090e0709061103040515040801050a0605210c0d120809060915190e0601060e15030411010c0c06020309130213090b 71
    0xc41d007117880da94051000100560010301200b103c6002858100ba1030140d42d046801080001621030320026041010345684c8240d44100c0141130359105101e0100f00080940fa4903100c14050030323840c0104101000907645800119070480100c000f140190101e0395031551440c280041502c503048005c0042010348024400014981e60f641e020b00b0048000303c00e41034035070b0b140101390b030b003034480c0500b4110784182010010b12054030740d004d010300d110300880108000c03101e44c200b04608207003008106503001402c0c2440300040c044028100c01c040140740d511000b1030fa50388000c090300c2e0402a58800c1e2507070010500110f59071020070314190400d40d03041d00700d0b010041e507510710404c5541c1708590042980181d0010004c41d0f030481d1400c0d60200007902e0f00b0400890468040c6440d110060004054140c0e1132521043d5034854921000d08943c8544010440c94071404080e42c4c80d00030086070341c801c02d0152501c40e44800c2c580203460913144400c00b040100d5080403000405020421701b0035420400855 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 228904478 1250 228903228 228903251
    0x90a030803040807030806030d0210050703090c080a1703070f08040305040506030708060909012f0403050a0507051f020a030e1909090606080105060303030117030f0a080a1d030f030406 81
    0x300071401244a00e481c640d5a407014940500a03203001404c0038841d42142580b041455008168110003041200c40003031140e82d003007030030307001460324002c003070300111041501003660080000c6500403c0c0c06100383d9408130050f000070340403d100032150040021444520505040d000c0c0300c0c00e9404c1482414000e0800b0307124008183d05400c00c07a04500000d9046082c4200380c181140500e810490b403800911017010100c0e20310303010221020f000b21182101c1000908494510790699001d190704c5415104240641d00b00241d90360b005001d080e100308602c6040040351107141514025540303441c0c004c0d0000390640d85007a1200756058120541010051020349441c1010220000c00303042d895100290138003050170000100c418a0300000361507803404003400314662300041030b2411a406525040c1c1149507440c895404c40c0580900040541000304803041d0603900400300900c80d00400b00100401080c0d460a882c1740c0c2c0004443c41c407582c01c00c100b0733105015403407801140e00034020a00850b080328540c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 228905728 1250 228904478 228904493
    0xe1231030f210207080a1b03020d03020d0f0305151e06030a1d010204031703190504060605090609040b010b0d0b0d111e13090f050706030f0e0312060105090a03 70
    0x45084949040c0903580d40307002c2a0000408901003103910040007043d00b40042c465031050030100c0904014000c45d19400c41890440303488014590290040d1200001c03803a000c1d50300d030800d5820b1800f0036014010400780c94403a01c03d1030b10a0495034101082e000b601000d0100c1c0140400050700e102c0307004446011907440d20030045015038044000010901810b04025070041d940242c5900c01c1e074010042000402d2100d01d80d001c103200000e0300c0303996070785481424002800003090840099401c0008110074131101d548907400302d07032040e10034107881d036140400c0000d0311a003110300807c059010b40040c03080c0c0a40718040c10002c1805080001c0d9001c046000580912034083d00301c0e55a00144100e900e01e080070960742c5c1010a9001148090206010018400b031515a0300200c031540c2c0d403114281400020350302c2d42d100c181c000c0306952580d5118000140030380440740d003445c905070400b412541c0c10f250010071111030710308621721500591600d00046030307a82c0c03042d480540e00410b0301c003020020500c0d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 228906978 1250 228905728 228905753
    0x5070207170312040515090f010c0c0b070e0a030506150916120506010e03030301080106060e270402010302211626060a0e01060c030306050f03060f0a0f020a030e123103 74
    0x5040007030a1901d209523003075081d00c1c070038400d40040100c1c00c42d500d0f0015002c50410783d0050f07080d0a14488104402d4003003040340640e68409441823196030144000301c2c01141d0074008002e81a110784902e69240a8980380b0b4000ba045d03580c0c0050100200000105181e0740701e81d4005405141241c071a15000000a1454100383c10000343c0e03035034844040040c0e81d0045074000c036910303041d581d5004411541804003c4414031481c032550100c0c0d80c50001d01168401d90441e0f003010040d2003400c195100082a0319801e0030202c1c0c41030140403801e0341001111b4000e52841d61145405901e08065284400352603084041c003811580d0015080c50000c0340c040d240c85150303800b0b010070b5503030f42117444001d01300141920604c8c0d01c0329005a070741d0802c48036237480100f2404c0d0f112454200c100e62136140c000505005105a030000d0702c20b68030201d400107480703034076030070860020750440d084501e00309400724003c00340d00c43c802d40b54440d9045814900000104070113a40f81c21000806181d1800380d481d2600c1c00c52414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 228908228 1250 228906978 228906991
    0x180c0e0a0b0d05152b020d030c0b070921060204030209041b140a091a190906080c031905010b03030d05040b0f0c09060705120d05070207170312040515 66
    0x2000b0660480c01d20306482001e5205802c0c0c410803200140c3c00020428050001d10300c0c15030b00d0054803120950411101e2070301c8000c0c1e0b010300700c0201d99040b410010000c0c03089030812240703055900003043e4030510464481c3d064072076074a81c08145450701e91000c3c02d2150004400c840d4560280000000341e038540c1c024901c2a40901299500409005d0310713070128014030380122407810801c210020300d5440d082c01203c00c0d112400340014403002e0741e0354040344c0c0104080c40242e10548200c2c54a00040101e11000121082c00400b400070030344403010702d9280e60f07030070b140c003901507101d0038407600c0c69860101002d40050040c000026013440c0d020103c5d0565110b540317220a1286c48400348410001070403000b40d400486150701903003030300341502c0e02d6001c1c0c4545900544615008603161051210034840454140f04408044c0e0751006070b1444040600710899151001d4011a840000e03450300c04880b1103403404c0b10360051132030180b080d0100c81c0e0340c031000390059603d8030401c1d03031038501d2582d8854614085c80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 228909478 1250 228908228 228908249
    0x503070c08060a06030b070c060905010603060b010e01050c1b01120507020606120c0108010303120f0504140705010f022d060405070314010603020112020c120d060801060f180c0e0a 79
    0x40c01d240d1282e142100240400e1540c5150000030070100310041e81c6260064620302d4084510b1b0080d080000161a500001402c6540381010000c2003040d994004c03d030140c4280ca84e54154072301c440041d01c4070700566003d0b04081c2c000300d0000d0781001040c50f1480041c68141403c010201c41e801c4034001701c50342154a600581d0220080c81210b1500c50780d0000c0c1050f0250040c0301118802c40020045801840024140880034000413035019881d00019501110304100b086640742174108003001c1a400d1154130b455005400c800304339948500c60641141c1e185400030490000b12251140b0f100c00d00e6001002ea14503c40b0b94214121340510119014501030380c0242800344c110b06020100c0e000d6038120f040503a02d0020b0400050340c00542c12440c072124030000503100e003990b089903428600d540d03107081c0da001000600210072080540c42901503c014200822480e5182c60340010058014081c03d03100d034000d404004d07840e072641d4018043c5d140c40c034a4940f80540340070002c20406074650300024200c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 228910728 1250 228909478 228909503
    0xc030a020f060a020315040b01140a0903060b0405010b04030b13060608030c070819060b1206010f03060c020c0d08030703060302060307050c100501030201170a02040f14090f0402010219020d050307 86
    0x40c20800007141c10021074070f011480d604003010040d81500c144150540215112802c001050303000d0507071086221022007440da91101c0d1032400910b05561800210303126442c01e2242d610030700340b0f4466241230714003002890345414110340b940384104d880200f40c0e0103202018419030000880602512009004040056895049402d0002d040c0007154020a00c0c41e44280b94461960001c980d03201d030110f030800c04c0002c008100e04089a81d0710a100d0700c120b403038411580005182910702c8502c004803801075404101c822030194040742c46952801c110703a8410003504441c800326194a00464202d21141400501c0d5a502d50201d480c5401c05c5900c1d00100d034000c113820320000d4082c80307440284011030400304803543c1950700203094580700310341703402540310142c000801414041d03040320f015046410103c45841e17035404c3c4c84616107c0b038094140c011804800401d20315180b40c0784490041368141c014024114003c02e440c04140c00090003664002d0000302c40c980400c0080c00104240d074068400078844 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 228911978 1250 228910728 228910753
    0x1e09061a0d29090708071d0303041e060216080604031b0c030b150108040515040317040507050109120c2106050c07020a060f0804080a030b060c010b100306030c0308090103020c030a02 80
    0x10030f00500c43e5043c00844002c01078a1648011100d00000000d100c02d040d08041402103072460086410040c1c0704400c00b5002500407002141c07103c2100e00a03401c40b0707007041c00d184d500d030388100e001d2281c0002c692218001c240040e001e50210381d419400d0401e29810b651140d1190140c0b03085641c01541d00c61504404d00c000402c0071800c400c1018000e0030a14003608150f41d486940b400d404507030007150045580460101449003c4070740d40c1b03001d411000340907070400e400e0803911040c480c400c80f40400c8600c0d9000a04814040710308000c203812020503202146003000f4201000c0e60700c50380003214061001800700144680c4a030303034090b680f01c515442d1a000940b040c40031200c40c90b009002030200c018040b498607030b1b10181b40d50307120b1b50214190707884402107902980a02508050700d9400280032684401e80e10055014440d4034004942001e1158038018065048075003a01000d84030450004041c008104403900809078558180b400516208011203120b055400000c02e00c401030b0082481e2040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 228913228 1250 228911978 228911989
    0x302071e0615122d05120301050301060911030402040c050f0a03020334030c0e090a020a02120306150306030309040e03030f0901140f1f1e09061a0d29 66
    0x9070001e0150030100b482c0944500c032103a60050001c0810080402015078400c05941843c15802d1748841100d9880300c40ca44c1100746a0800d00409002e036207032480006000d8114000c4158025101080c5480c41c0c903203400f0710014000c010a000203002d010041c2800350300311000140700e0340c40f49550050f12801c080d451640860b14081241340e00d50000342c1c0c400c01e4610303211050448013119090024224500580c00d0b07444482c8103500360f902c25006d104205184625070001c15246080e91700b582c1000d43c0809048805002c1034034810b400c2600c25102d844144000c01c02580c0005008003101e040840d90703000035003640c1da0403060a820b50804418010811f482e5005507401c0101c55009002c40030303c5882c4091164002404a50420300c0e17900071408607100c01c07039000c041c80e03c420840381c8020703140e58480c0d01c0c060042500710f1241203a1400010300c101d240c400c86040d02c5523150480c0c115200305075080e0360f6130045000c00106a56034082a00c0c0c000183c2822681c0600608011502e450414201b04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 228914478 1250 228913228 228913271
    0x30a1a0909060601050d0e010203160f0807020705010311090907090501141602040b010e0904141b060301090b0a0b0a0c0c0b0c0a08160804030c0e0c190302071e06 71
    0x5005100000c01d0000030307a00802d22691210007031070320985560107840c026000d00030039801004e09520010601545c1d070740030000280c2c0109507840300310890107001021240c01c0c5c8200e52130001600481018000c9601c00d4010100349030183e020107041854180c0050b02440b4195440d0003c940071400c10001c558102e460704a9080b5a000c91608021410b1310700342d815140c5150091080c3e64511030302009078090810441c5000020345805040c2c0703024580b000251451103100d0130144190a08100f0b85207507e0079501c40d0020203021981507910b4050385002801e54400034550003000d124010840601c002d000c3d0042e00c10942c5c035a980300f042410556103c101c6a0030001d0070a80801060300c0d510300002da20f0701125441010340760b6420081044450302d86010b90010041c2e5030000e000070034860005803183c03c1d035442c1d10b5000c030380c4d445e42e8000c0c42e11071041c1d0703c482000d044000d20480e0342600136805018400e000d840400c80c5c2c1070305405404603501c4541340c12101c0d990346000842001d2180c40d0050b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 228915728 1250 228914478 228914531
    0x80403030e0f160623030402011b060f0501090516051605191a07030203090d0f0216080109020306010e2202060f041502010f061406031008070e0417040302010f08060312030a 76
    0x40108080c50644c0e142c0700d106c0180b01034180040c9100003403948034519a4038101c0fa805c140200800080c401000011789028400c240c0c15504042c0850740030b00e03c990281c3d21001650b11440d2405c04c00901004149180260507105c6024082c000440020301c0580d00442d540329041c40380f07030100241450040c3c0c180c003030450b9081503c10310822107071b1040013400420100c01c50400c50420010400c04030301e031441c01000400e80582603400002c1c0001c054006d951454401c5044d40c6950b03807100106025414211100010240305007038410081641e600b004980d1800900f20f03e10f441d17442400c43e02e607584154070528940062048115079580c0c2803142000c50b100026050100d01e24110361055480000080b2500c01e900000c04548664907605601c0002e0414400707039518956646040016030f107045030103907204408071209044c5d07038000d00c0480d425070368140c454018220030786c8011600e59074001c0c190340d01803141c02c1100031000340e80005107204058001d0701042c0030107484852100c0741c2074420075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 228916978 1250 228915728 228915767
    0x20f0d06121212062c0c0306010c080a11031603021606050301210c030c031514010e060d0b04050105063102090a090504030e120a03080403030e0f1606 66
    0x2a20004000b1001400e140c0114034114244500c03596007880284507550224814075201415004400c00e2070800d03810490701110810015070f152408036030244030440395a4000745004080400045414000c1c05032a4018505002d4200c201410380d440d40c0e1003514600f0180d6450400001094ad0402c01c800f41400201a4200000e2030031001410300c0c041801f9841c000da4480038441041e5044420401a1940060102c0300b065a00c0c14269001c107114001952241c0740046400c041c028180a5440708200907501111300360b00e0f22101418114002d07005039440290f8000c6040841c901d44c01c4240958004c000003d0705041090401c940e00144401d20800100860601c010386e40c1071401c8030012220130400581d5501281002881e8600c1a80000b807000e450310040c0030070305038041346800d502c04013902d080d044400000c214540c2d0f10300409004000501000001d00000d00c00e80045100001207400c441600b9240c82100342004483c0d41c40c403d0000320890308110980d0311900b03203c0c181544001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 228918228 1250 228916978 228917009
    0x70804081f06082e090203100f110313080a1202030a0e0c01030c02030304110a080d090501030b04020c19020105040b0f09150c070b030c0f0301060c020406080309010207030b13020301020f0d06 84
    0x85a0390700c0700450080d1024840c00c9900d04c40352075080c0c10600d0140d50043c162400000c213455010000c0c40207041019039140b0b4a44071012400c2000c0460b40500b10046881d0603103952a070741c0c2d20099006880d05000c000c403009612080780020f001840c0560000a40418101c54109003076180c00040d80740c0da4109410440b10b0340d1529008001c40350850b81080e410742c000c880784408584030754480d500030205481001004070700580e1100d40c100c1903c0090380c00380031a03501802080140c0c021401242e4003500801d9505141d01040c54070315141c00d10604116083c66a0340d1201021500401420714030701e0000a80d150440c1303402039840103401e021424580c14141d0010106560b07800c075004500303c2c400700001040d8501d4040c0143c5d00c980c44040c01066403581c40c0d0800522048202104038025801c2910201728444040181d5013402e806900800b0603d14540307a40c05103c4018000000c151300c50003ca0780561020b000900ba80443d1420042c0d41e0490140c40004a03201342e13210041f158280103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 228919478 1250 228918228 228918253
    0xc03150506071e170a0f090b0a050d0f0c050403060b09010e18010b0a14090a051b07030309050a031709060105011d04020d090b0105030d020106080c0402070804081f0608 74
    0x1064405042c0c1080c1c0403801c01a0f5900c42c4200050fa0780b034080d00440340b805881414032058030040c608010030f07030349550000c2d0b52a40c0039100e01e51a40208003030800c1c01e00c030001d100c904c0381000e040711140302d005c040b910002109041c0c0460700301c0108800007503800a0f040c02444524000c07107441c0a01590229143d615005d8001980703032014040103c4240c886800348107a5200b504030400800d8001d0003842c15a41d110980103603400b404a503240100008800160300b62131030310446204074108910f65240000c13a40c450509580802c0c011018599074081440100e54100071010f0002d01c00d80740c0d101603043c0c1503000703521b60000520507a00b0307600400040c422640d0003410300d242c4c030180803804002e41c6940070008002c0d0040746e00300c880c840d20b00000c800a01083d41c0c1018104d400a8041d00c1ca922450b8034124287c422500802400342d108070031a0119081075402829100c0c0250740d05400c040d21540e409041040c1e620303034151014030041d80303a54030f64050301c5440000c1044100a010380013158 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 228920728 1250 228919478 228919489
    0x50901061a0406050901050d060f030c0e090a020f03070e04080901030b030a05071505190201050415020909010e18030c0102090102120a0804030804050c03010606021e010509060103060e0309040603060c031505 91
    0x24026401000001724403c0c2c040e90142c1d0981d55070710600b6205100d82515800303075048454441c8001c4c2c0c0e42103201e00300010160900c4607410f00034032400000d00303501040c0c2e030248980c3c0300e800700d034594061244540009035140b242e00041c2c01340f88100600c0d90f0f1903c3d400001020350342000200c602c17a401540349007000a0780095108216015100e525001e4040300209948038001c03030403d50419803084092200c02541940440e11443c81040307002004a540551841240910141c3d65000025800180043d101c0c02c650107600c01c11048003000c2e6a41da980c600740c190b4228602002590390089004e0015680600040c5501303504055401d041411b5024014040c12015001030140010000400d061000c10310080e40a00b0b8054001d00110390703501002035070340301008818071682c038145d0300520310b00034103002d0140115011001808540d00316141c13000100340c15400c5040305d01c0304218040444c2c5031401640021400303038071b00041411001340098140d504002443c0313078140002ca42480035a0701d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 228921978 1250 228920728 228920737
    0xc0908030c010f0e06162f0c10051804020309030c0f0601030c0b12011205010605030d1808010c02060106110304080a0b160801050a170304050904141e030304060906140703050901061a 80
    0x181e2500b052010f503d500c803105110250044600c2e07800c292087ca0620510000e5540541201924180c00c83c48000c6412201c0303000740d0040c0090106804002403072072078290080d60300810030005481c5460034a980d074510382600c0210700d200c40d42140c0d004200740940c3c5c045440c003c1039a100310504d02801090003c410a4050003084c00101e26948640d00340442540300c030700900030142c22100b0503c0b0007000034200925105441c00070040c2ca5001060041040c02001003080b42c5800800850342403802c1580e441c80b01e01c68000031448207000001d0752000c20400c0c01c12240c0110503000c140d0805d201d104962154003404682402040c400420081e1280211001107515414440c0d8010f001450068218070031503204660107040340090009000c060407911848207a980c04582002401c614500c0f01031a203d400d0001030740081c00010b0114905803c800042c6214400000c0d1103807843c040003004901c20b40d1000000f0f0f41c0c8004011050b03500f4494107000d081c1e4805250b0712102c590603002c1c054801d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 228923228 1250 228921978 228922021
    0x70309020f2707120c090311040c1b030e010f0206100b0a050706020f04050a0e010b090603221515050d020d060b0307060f020613080702040c0908030c010f0e06 70
    0x1d408000b1801c50300002c4a14590300031440d0510460901c020700030300d510b600849201c400b0f07240c00030b80c2984030b0041c0c424504490f88020119044207100c0304010081a120010f4001c2c00a0ac1c1c000344046081d078010521410f10a442c1d01d0405800b401c0010134000d003101001c0300b90f5219405121005248500001c211107001c0103c60380c2e0741c00010100c0c0c1d00c1c02000001041103001041103517070f9030340b01e50250064480c107840200301c06aa583d0404a18002841000c9582c0c2013003110b0149410003000459000910003108400b002607400f21000000d58581c1c20b51b0308500040e40c0341103141e514020b801440701500c02840b0780c40e0806000880843e203e401c02403051514600880403c001500800300711340004050b00c02036a42e5407806029580d040c0c10705001406190002061611140c030107625840d005000203040179050740c2480014a82c00d0300030400e10501540006204c02c0401c01840020904400070921005a03104034007507400b8640c060503150844401c0000c3c04004c0d100c06142c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 228924478 1250 228923228 228923239
    0x1050c04050603040b18030403260703120f0207210e03240a0605090708010f151209060e10060f050303160b0718061d01020601080d142101030b070309020f 68
    0x482e202081350009005c01103801c41c87c00007090000c240004034104101e0100000100e4100003010a50302000c3d108218004000c80c11400c00f1000218450740f180c0120103440100514014031794644018041048000c000c0010310001000c900640c00150ec1801c1c00060307005114002c0c030340040141d29551b4288101030444000001245200c0c40e4000c0c000610019001c2c058030308002030010080b81b002d02922285650038000010ba80a000c0f50a14000344650348a69103000d59511040c0035081ca51415100d0540b11212a00300c00400d000e0440d00c030304040f500007101c03031070455401d10118281e40300c58030942041c40f600143d5254208407c01450740001a46090784e510b03001030f036280ca12000b02500884030742c0380c0030484c1e540026041d1090040d00030710f101580014001280c1d40c240034017540100d0b0f00301c5500700301d409008442007080d1504ed000140d080044503a4996000035158034110f01200350617004000b845841000507801212601e010f0155030302d1070700407a61104412802c036000d0b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 228925728 1250 228924478 228924481
    0x20f09010f030b010203090607230601031b0807180f0e03030108150108060609060a0801020d02070c080610090c0909020c0307060b0d0c18020d0504050d0f1b080f070f030201060801050c04050603040b 87
    0x120b9004c0d1880702901c0012118642b0108401d615980e04090100f00c9044080c5029085a4022000b09400321440d50006190007801c105060200e00c14003442d2040e400e48450b01c0402d404418061a134100e144c200c011600ca42c0b601107214a88140c00204890460782ea1005000b0200c1c0800c0e803981c008419a140f0b000c685500000c01c904103210f510140d0554804580b4100031889a001400c0d040e00480c408613666441d000c80644540b01034881c2c18200407441c400304010100790f0030451050b080c03814192205d907911903e01059900141c07011045420000342c4038100f20b2180b164143d820000c2d1001c0310880080d56580c0604455030240541c44d00d83e509a043c2c10840c0c54044481030200c541092146050034940725580d000c0130607145022508004c0f40255003403148503000d01b600040580650040e410340ca40d94800d902401940019940811500021618440101c0c40b0240f107640005032240c6040301003421034901400d078001d541c0040008104655621007647d0b0440e40010900409 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 228926978 1250 228925728 228925733
    0x1170c09040503070b161e051e0d0e0f0f07051e030a08180f041b0e030f03030c070b0114060d0c0903021f02071d0708090f01020f09010f030b010203090607 68
    0x550041200040505c640c4000304403503403c200c210b641c010001e58540455204907100d5601481c058503202200044080c40107640c1180b03410b000029146180c0b8009240810040d044420340b0070100d640c407501c1d8000c18802c285c0c800200b1030fa401d650b0a41c0702405145040000280418940002038003106440c0240340f0700d0381d9001c1c8245919141d00494540c0e070b0740d8446400303203094a0071350300c07840c4030300c0340410600860706140c0242800440040b581c454071426500065a00c0c1076031071101501842014180c00c2c020804000840c0550420720980d5218001843c1c20124504140c11000032590350f44910b101684030fa806440c0300c1c0041c01008100030b83c582000311800e0f4a84c1d44080c1d48500401f00042018200200900c0e47d00580e5098804a6440c0c40040444045441c0300c1c611003602d8400003960a0311801500e030308016680b082c0d480030401340c40c1007800e91f04201441c0380c14080014901d0110b60304820b02d41035101c110f00b018016000c030b80c030010b034072401141c06041c000d80002485204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 228928228 1250 228926978 228926983
    0x30703150611010b010f120207061104121e05100504060b040c030c09080c0f0f060c010f050115170c0c0102070203030d09110a030b040609080702180f01170c090405 72
    0x11240c0c5120003048040d0340e180402490080c2c42880310700c0c00e528107041c01016503c00c83c12840e40000540b0f40c000c4600001d41c0000c029840b2072410741e0015511040300b45000c0a90008000034007541600d4506003201b4181781b50300307079030702c1012001c81210103400c1000104041107010001c07400b40c0c000902540c0b42d0070083d0150241c03000450f40305241052000d12940c140d8021441b1000d950349858885444e00b2509554004044c002e981c004c52055041c9a589480c002c910324a0201602150400880207100340c291103c106507400019100c800601000d12a0110300d0700c030000a00d021050358614964001e160704011301001282c141c0004c5000040c130094040324100380e4007034226550742e06004a49001072141e0502202d400b03070404e030881a90701d80286040c0589401103030031191615a072b42c0d034000402950380201c850381d50500000d00036070745044c1f50141406564002c1d52262504a0381110300705016009818030030620040d00c03082e0a000120024456401c0d05c200c80e4507180e6081c00ba1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 228929478 1250 228928228 228928241
    0x32a16120e030a0b0709080705011e0516060902041104051f090503151b0702010f050a1b0b040b0a0e07270c050a081e13110402030a02070201080a020717030703 70
    0x7030b0944104403410042000e1001c3d01ca114194955a10b4110341d02c0300d01c002e445008034868030340050034030108109000c07185a40c0703c40e00c00a46c2001231a196900510540040340c140090752665520f11074001941024007600d03c0030070007400c0f210328050a200000b454076200889403c060410080c1444400d406810701e100034100c010300b1548002d624002032694880d0889100c0440719591146503c01f03001102940c2020381e05071104481114408022650703a0000e0701104200b1060211040c0301240f0141d03456026030060011858a1800381084440740d480a000c15400500c3c1c030300c10f4480507202242600c2659590f203100c11040703840d4044100301416074920b14810328545241071415580120040070a0041034844000541d1030000c040d400324000a02040c4060f03000d000616002c502219480f8140d1044800300d0340041c18038082422138208483c0c0b03080b0303d540040c1003425503170001c1c860b942c010b090000c20751400d05640e448000011400281410b00c3c240072010925240c020303000803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 228930728 1250 228929478 228929507
    0x10b0301060b13091a0603070509100c02040513031d030709020f0309060705040f030305250b0601270509060102150709051c12120f02032a1612 63
    0xc0c0001d5488040082030b81d4018095a00d10300241000003480c2e803842e00840c030b81e041d03400c9848000d1441d544241700c0d25600c000c29000402c02c2c100402d111a035078151443c20b01d04800d03551400080c00174414131080710800f0b4452103200030149049070010364021150301c40c1075119007504e54060880c1002c070349825015081043c0150010560400e10401a00a0351254041400b00c98054032070040643e0103104602440945448000c41403000c2400f413401070406140200e002c034054510303144108101c054003d000c40b080d042030010700c407541d0f07440040c001580e0004800110000240e840c0c0c0103414041d803080e9400380c40d0f10f0000801d940e0007407000e11700050303041d40140b84c24507090384001c1500345103001c2c241c0300d003003075502e44d5610540000e0f02d10203280d0b100d024211a10240502507526500001c014071100340c0b10000001c4100c150b0001e58050703510901011300742010b074016500351000c5810441142481030100702007a040d110b0707000c00742a401c0200c03010980b40030041100c0b0034241c500c54 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 228931978 1250 228930728 228930731
    0x20904050f0402030601120503030606090a17100501080309010207090c170a050402040c0c080a110705030d0e0306061512060f060313050105070e0d030e040912021b04050f0117010b0301 81
    0xc1024584020709400e110b03500c00c8041d43d03641d80e02c0b03100000071007159020142c00c136402800060440c1c00c08000400c400e11004020584803561400d0b03440425600f0245050fa5410079080704076000064000c0d94050182040594200322841f03000035981d00140c405d0510042e103034103070044428000d840c0c0d014040700f807900c001e21034a090844540a04420741c2c00324000c900e04220414a41d00c00c44200c0761040d4003011061401502c0c100881c1c0d082c2d600e0302544004c0c080e40341c00240c165404c10880d1010306e015141c0a100c9010117040604260004000758025889541201012072041c81294045080d0888201c000e0b1034038000700c0c0400e44d4500d2103d0300003200006100104a40c3d0050150f80342c450700086c0f0181da00c480046803100c400b0750070650010308540d411000a402014078640101c4040e10009007024603440700d9100100e0000c1c00302c01b68100c09d800360240002c1d9041104100000c0e2010b00c0181031444401d542050140300d4040c40104041028440304806c1d0042c080d00c0200800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 228933228 1250 228931978 228931981
    0x1510080430092c04020a0503010c020a1713380409230a020a030e06070809070603020a020303070807020307020d05030310080c060412080c010501120b09060f0a0f02090405 75
    0x3186106804007070348480204101030750002d0149580700c040d200c24401403000464145008660120301d440203070040364481002500801d0700e803400d00c50100c7d016101e41c0240709884040c00c01c0000b01400e80d0344c0700e207070301c90800401d101803044214642c00c81d00741030406005544800e5040c203a0744080d103180c000b030030481d214408131030594002420680b091007804000c1e40d046046580c489003180000800300000240000d90b120075698042d00410b50b4a00300800c0d0007556507046800d040341215100b020412050500c030030b1580421580000c2c2031242000c40c40c00103103940103941c0e0700000b001c6030100601180010307a0b4038401c0c400c2e556210b030701405004444610380361168494004541c4603042030844030001031040c00000c0c0451000300003900117403803d4200025188100d5440c88243e40ca40820000007202517001d102d130500034040d90f44242c88041c400c2c5031040120101070190341c039648c030040500400f90701c215001e0350881110200022012226a0200080d00038a841107030701514010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 228934478 1250 228933228 228933293
    0x11d090f0d02070e091902041a041b09080f1c110a05010f0b0103110301050904020d02150901020105130b180f1209030c010309170c030403020402040602010e010515100804 75
    0x1c2110a07a0056106080a6903c040c5c2e05e55403403615551442c07400d401e443c07a03040503007400d41c40031f04c0200180307030404580200c2d5030204003621080040c10b44502101000b03030035201c0c0c3c411a07410203403408002a1000b0480c2503511b91f42c80c0021680c04c000b61080390071403020980202c1c0c24040f50044a0140e0780380810340d0500f90f00a0084440300703100d150400e5142d402c20342c441c2c40b40441300e403035614901d0304603420001481600c0100074401c03a006003440c050b00e00913a2f01c40410f0406460b140c005156503809043c00242525005400c1c0400309400828000005141e10305850348a0200042c001d103001d03004490310301c0c015048500d40c038a400307090002a401106c075801450400c00c20340c1212102d4421000450489001d00c03005010070038001090095441e00d08014082c0b9140b030707001c881c20581c9a40024041740c0c415400040941c0d900d82900f4120542805407507400480390864007014200900030422180a210b00d880400203161700040c100501d0080d8059480926003000c0040000c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 228935728 1250 228934478 228934483
    0x207020a18060312020a0c050f030304090e12220f0b0405040e120409090311160e04050c0603011d0615030c21010b0406090b160f020301021e03010906050603011d090f0d02 75
    0x5c0c1064070120811787d001b10b00c40c208046140b608142c0130b0b00551070326141c02c2098000b0028440342554038020b00400100141026002d030120100b03d003152500002031f48140c01c40412241c1c801152074090f00300401415024400340e4044420594000c1071481f2010015030078080c00b001c0c0c40c081405d000c1004030f9640400d40c00000840d20907201c030360200c0039141c505544e45418020032107682030503610078021203e03020402a0000e1007a8212080000b00d40c00084094000741c11075a060840454400d4034802000b01b03070364100c10290b03540e08101e0550b0b0321a2000d0b10004110520000b00064081481a8410300004170300303416180b00b030311550f16078000100701e40c8184a210001102c480c00401c0c02e0203410b0850b001400f00380d004240b80001c6580b40102501e03c0c10781aa13065509010092103411803500c0c0c007801a40490005540e50b05244d64002290126088117005100600051011402c01070b03200d8408a001046022540c2c0c48124080c50021401d40000290184181d203040c4107800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 228936978 1250 228935728 228935743
    0xd0b04080c070504020c0c0d080c06040602090918060606130302061b011422060603050114010906060201020a091a1e0306130c0804030305071206080a0b0702010207020a1806031202 79
    0x12007003a00c1d0300503600c3c0300700420380c0102900e0000b039410035445c250f01880c010b0728800300544207400060804000c803000c1800c0220848040c0d44450700004c2c00000c41c0340061a013a44424031410540200c1c4c051010300396204402000340340a0000003460143c4010200103010041d60300401c0d0640d11031546841c0a0140c130100c40090481d820012241e10380c42c00150414450711900a210074080003d410140d554102e000c03040d98000da4030140400840c40030b0060721000b413002120305690b54034000c401c10460ba01540504210391052001074520395121003c8401c45485002c8209000300f40c0c0090011885034051406265080105065504024101070b500c101d20071504081449130900101056515003000c40c4c00080c09180010700181c003c0c0d00560300300c0e21600d070075191040b24500e0b01088234000e0700320250a5200328441000c000014080b00e0380710a0314402581419226808518a0009402540d680c030220743ca11903401000c0b540808000e5800040512450300c1500029458148 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 228938228 1250 228936978 228936997
    0x504110c190203060a0c0512070c030e100f05090a05030f0607080609040b01030204090c030506010b07230c0607080d020a0306080105070c05120c0a12050406081807140d0b0408 77
    0x4001185904041101c030300005070ba005806004250342d00d101700401011200c141000303201040c08886001400094810310902807511101f50791101801e01610040c10000710910801d062420703029041c0d07000690742842c06460401d1130320780318410000740588000750003250301031040040800305840000341c5a401703074a694035684001d0f1103d206101e0140d8085802421000c11640100b00504256010b411118002e0400c0c00006031a940c0d17203420060300380e111788a0300710302207810070600819a500b210708031004a40c02042541c42c07510240c0300c8804201d03044c42410041240c2c014804808100da004904228086585100c1540003074000d01c418003d00d00f07590300e81400101c03d18050078510b41000c0d00a00104400d04e60008c0d00080d0b40e022402c080e032107000d2156070348006024044a800c1c04c048940700d0039122401c0c02d40080c811900141035140342d0b04032a40203c1d510790040780c2a000c0c1c440e00c8550b080ca03003040c44041b620b441903500d0003e0003008200c0400051094904c080e020f44103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 228939478 1250 228938228 228938233
    0x20306090102030615070c05012d1d090f070c03021f0204090b180402090a0b04050109020a0206061c031211030a1509020a200a0807060b03060609160f090504110c 71
    0x30f014403117125503001d00c803801404113502000a02403580181c7c003100d031565000d0700b1082c1e040d101c20010b12440302008600804141d0001580d51030480151122040901c29190400689429041140c001c00701600d2030f824003100003822000c0c148248202e0ba44070f007a00c054035120046203407000d4025070042c400e854000b8901600b550151030050008003001303061090001c80b94a9640030440311920180401e40c800780d89510590b00d40d00c441c01818001d02c4a403030010780b10002104041d04201c03000f03000d603101d91401c0c188031400c90b00442c03e003d100c9402d4500346d040020b064002c5001000004100201070f84040104080500305405c030301c16280c0c141500300100c95440c0c01c508103900407141e2880201e200a0307a44404000031188043c8040003000441301c90340074645500005034407140058401c1c0d41c49818031512401c003002520340040081c0c940c400f007460000c04020640322006440301c1046030140500c015148281c1c0702c0005420000e100300404c0300802c40000e00d80c0d01030141e941890 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 228940728 1250 228939478 228939499
    0x42a020a030207090e030306010f1107060918050402100e0103020d1a0307320a0302090403080a050603031e0717040b0a0e3304350a050d0c030203070203060901020306 73
    0x10043ea01804081c40c0f8111700642c190740307851005451303150380d9000c0c05040080d404481c00b080402000f4100003090242c84030024182042c010100c2100c1444208180d603003003500b480700580341d00380c80002c500640e2400318034079019240100d000e072054110b003120180c100060b0048502c11203001c01c0321114110120b070320703155882c10b44a409800c60924405040e481405d90740040085540d0350380149402840112019144d500081380c1e10000d030341c01e4000402c2d220401a41c04080d115550f00b000f4120001c504120640309880082c12603042448941e02001c550303842040201030440c1003078102141007503111a101c8296102d150400e1500707500141e04401d041c1c8a50404034100d10214030a0691341104140055501c16140c504200003941c400041000083c0d06030a000f0000700030003284600b40c02541c0040782118185218172400d100358011854000000d00c0020341081d5084c01380c1800440004541001d80c02c5005088029425010749420000c45000c190b005500c03a51049075040140c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 228941978 1250 228940728 228940739
    0x80a03050717070b0a050712061a09040f020c0c1903020310230403050309070504060308070204020a11010e01150803210601022b1103070b0a110906070b060102010501050d0c0302042a020a030207 85
    0x1d2701d45500c1260b0341001981406600b4080400090540640151001c5034200d202107060040343c2c401d941c2c0038100d4014000034403e40c500101405010000c295003000d1403403e41e0002500c42c800d0b400301c0603103a0b41e07802540402086400b20460224100003c00440345007d04018081d58400c4070100000e006142c004031b014a0b2900c60041620b80141c581400c000d030356820701c0b00a510000000c8213001c02c140c04003c1042c8240160b9075031445072000481c005c28181e1f6901210aa150000c1d030b425001881101d0910401701e81d0b4031184601858008400c0e02d031440143e04004c0b4500b04d9040740b050445500e80c00c2041c6030024180009142d648078400d103041c407481030b02d0313000d03004c401002d8900c0e6001080001c4000d03003006441451036131a0510340403100000486992040c1d10481c1c2411004081181568081c07140900405060b242c202420b0240e40e0b43e00d05400c20713404001c1c0700c1d99071440070140c852600d001c3c0c8169204481184100889850406541c54424600c201c1c0144600000402d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 228943228 1250 228941978 228941981
    0xe040c031b08060a1a070602030411032b090501020604060c09050a120c2c041a070305040b01080705180c162609010c120c15060609080a03050717070b0a050712 70
    0x100f0031005111703d41020802d94175040654400761083d00c0c0f10b007150440e1011170b90b007446a0080300140403e502000c0055214240c2c074030418018260900c0407013030302041240d8022072426481540302c80b0016550000a405540c4a41140c0101e034001114220100d8050100360541084070701800d03c0b5122566a00d000a048560344884200a9a40094410296400c0c02001c5800a20418010103400411150010460422213085000a850b00300307001c24089030a4446000d41a000e000d0310603141842c0204290300c0b801c42d90b22404003404c0c00002e15404030002540c0d6001007501c034140d109070b024205000d4103401200500e24024a80b400c22510507055001ca801e00c0c030068445c1ca010f102141c40c1c0c900d003030401120604c180328401c0c0c514070000e0350340c0c0010b03c5040c55200c400200300f0b003088002010041c2c0c80d00034a0301503018a07000004250001b050f100003952101d0b4105083e40715401c0329065004100000781507602c504280000120642c02051003428256510030f4070300450000e080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 228944478 1250 228943228 228943259
    0x1701090c0b0d141303201e0106090509031306090320040b04090302060907080601081e1009050309090c0702090402041d2505030a030e040c031b08060a 66
    0x108081000c0c6800c10614142202401d00c1c0c01c0400d000240c40070700045158450b000444110704c0440000510a081540000500b280e100b10140700c81c4200c144c10754401d5560f060184e250080001c5203c90a0002c2800d4002102611035401c4c240058103104800c41d40e83d8201c1415021030400c845008681d4600c608801c10489420161021164210010a401c20b140d25040d06401c1b0317860310b880380c0683d140e0380640c000007407082c0e004081c0c61803c0010941440242e401803006508080c004210540300010461220102c0380017000c2e00034841d08a070b41c5031500c801c04081460707042031401403c1c0000030015041c411010703130304081c55a940d107040c025640300c2c1000080d400451400464051306095000d0842c2c91449000c44003010018803042d890040040101840c640324205038072034412110145000902c010341c010030350142260350262094100c0300405010f15500c3d14884900b40c800d0704011407455900401c415030064803000100b89100071110355000349070b90000003031420080300554 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 228945728 1250 228944478 228944483
    0xc0306180c010507020604091a03010605030f1f0e070f0e2809030509060d0203010f0806100e06030a08070303142202010c140d0507050c03030a080114150c0304170109 73
    0x1c1110207a00001507580c1c4d0010760003039800550511001c00c4000007881210b0500462540100d80500980101400d640b040c2d080b11340a5001008060041070002901ca4024a1540c8000204d81070010480000302401413042e04a4421031400060340d48000c2d40c0b0400f502c0800c03c5d081c059981d058601c1c0d64100038412105526000341c46e03680301403803555014242640c800d141040c6810400e40006116400420b400300701140d00200400440034031941c07140003803220001401281c0b42c200a0f480c80400700384510309d5a140c40d04d0000d45295030900452144d99486410a501c50003030b401c0090082580b1078541829580ea4004a00d020040414440209040581038105c4594a900444e2807509600d400c0b511035040d0525210610003e1148165000c01c5507202d170384900c1c6a040140c42c2001d2045c15500a0b0010030000701c8642c0e000c0e010030f064a1203c85441541a50140410440702007030a14030380241c80401c98000384031022004004840d810101401204401c1120500301c0e02c184600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 228946978 1250 228945728 228945733
    0x6050a031802060d0e01061e0503061b03040f060609050c0d1508030a0e030307080a0305040537031e0207060e120601061803050d0c0303060b120718170c030618 70
    0x100c0c500c088a030801d4030118031810020503100c2c0e23142040c0b00000719190b01c3c2d0850b4584401c0074001c5080070000c49a1240907440c0b091043c00b038601701216a440080c00c003801e041c520032849010700450f90001d2004144005c0100124505002e018401e600214000e00c1c1080c10f245890904c021481051010f42e89910081d51816040000540760315500303071070068040c0400e10941000c507240c1e402a1042c05140d1310045030601d010b1400314100000341101c15220040600d0000200200c489143c00c1c42e100c0d0720f1015442d640d60b09068500361040c46035003107034000d110700d00803602d5408105002221103c0d02c0305004084048104082c1240e8012407862550181c001008450b20803140c0d44903641090303807024a140e03160340380d007410108800c6140c1c0c003190000c00c2c60001c00d0340c18441c0b20020480c06a840f41420743d6800c00507508140945400c08020301c1c482d828401841c0204040c00034045100a5600c04614a8403241c582c0c08001a40e8440d000300300024021158010751440b00c03584441c007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 228948228 1250 228946978 228946987
    0x20f0d03020c0609040902210d18210f0606030b060d0b0a240609140109120303091b032d0b0f040c0f0605030603010e0c0a090b060702030706050a03180206 68
    0x10b009007a000f1303002043e4000c0c0c030303a81e0030340c0581c884081e010000012500496a80360303500b03034401d2070074810410801c20071040b6800c5132510000805c03080f0a41d0075510900d0407100c0e88500d80011018003440c06090384a104207414104801030b03000c001280c5c41481d103500c0310303074138081082181c03c141c1c503014000103403141c00141d4202e82a1300c005030008000e00030280303014902c09800c1d110505a0001401325402810502251180704005208030b1002d1038402213550070140c88015180c56a0340043c00d158032034401c0c000300300402c80b4890392042e000191440003542c0e81480410034008840920149103403180055429445038a00c40c1044d8210150031b609841300b2103011346800008209071340e070440c842c3d0049490700100f440d003402072203240e49280d220708040041608542d46103074011015070009d045c4120940701c13100300404039503100c0d500045c219040f2012400d01e01c01c01c0340c02503050040580c08100e05400078003600414000d503030708020301c07044100c411943c45200d00002e98810300034003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 228949478 1250 228948228 228948253
    0x60c060908040305150709050d022d0301151d041a0702031201120201170702060c0d11070b1e0408250203151b040e0103030e0a1d04020f0d0302 63
    0x8100c105414071948080b45850342daa110103041080c808001c01803407504000340482e691b0710080c001e02500c8212202180681d090b03002030b0303030100d03040201210765070411030205080004680507850980041c00900c0742481c1c09003070110301801c40c081c0200c1030b07210101500f0040b8441c4c081e184106d900c07880640840d2030b8900880000c20000b0301840851008201a0122040082c8558020032100c1c40690012010b440050b00c64540b1080c410462100401001581c3d580026041e4010103c0e400c010760300c4081035005800307044045410a540e0304001408070030850035028982c0f040389207103284480119400912a2580300030303100540308110520001c910310328a03501444081141400d00071444455a011900b0302d50580c0fa585060b0a00104000361200705200e004c240300b4000d010145002d04050340600210302c113000c050b0800c4400d040c0d090700c984403491598040c01d104011282c100306094682907504000300ca080707000754083e81c07201da10760404030486092154150085c014046015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 228950728 1250 228949478 228949481
    0x8010e0a1106040f0e1501050304030e091905011401080705040b0d050a020904090c03060e2b050408030c010608010c030203010b1606062303071208030703020a090b030112021207060c06 81
    0xe80c0c40c2d40c80041003000040c40204840c05800400c80c1e0f01406941d49001c1d00607094000e00316207214140304c4200204030000703500c0030f100c8c943d241d4101c0d114013558648004034040c440540305503601e55480c010000c1900031140150002500003682ca00a055441e24402c4680d4003440c461118518400c0c00300049a04403500003907403003041240d0060914084100090594a0f00403082d10340d1200b803002881404114000e905001e6034040081000124003400b000074000c00c24001c150b0000c404c00240c40b128802d0301107800800c000b0003106d85503881f20200b10f000740240d101d802002d41c6003415a5450034002d000f601e0407a0440e408090604108130241003115461020443e9443d80d61000451140443d9001c4044488c000c5441c500e00000102410700e029550742020340d01c80c103002c182c4000110f0001c01c42e42d204a49213405602ca036035085058071100b0300c6801583c813240010001144000b240030820304028021141c0501100c921130381c0d261116074900500c0001001500c40002041c0c25 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 228951978 1250 228950728 228950753
    0x50604150822081c053106290307030b060405130803150f0a030506040206070303090203070e04061a0604090b030a080d05100608161215080d0908010e0a 67
    0x104001440d0421003101c150100100c42c00101c07120a400300e140300364043c01e604010182072080204012034104407040d00744d02d44000c0c2d410035101201c00c106040d001c00301181104c49640c8a10180010341042e41d060300c0c452001d6001050b202040c4100b800d40380340026900c2e04403508591040d01d15200c003001c0c00098200102407503404d00d00b80c008000018003460055119119180000320608100000c000560f4104006603126180e00c110900108501052194105904448103030b6105000d18096024000c07400019605010302c44c0b00140c20015004a580325602c03400040000000058290940007008110280c002200780006d02440e80c45a011402400c4001d0450700403800700d40d100f501d1a0b020107041c0b000103889900340f2605900103070300c4402614050828404501c0c04540c02e2062941d401c0c00c80d801c00000f124400c540381c440d503000100d10103001020410031522400c0fa60b59404180c0c1300b980000c0d50341c40e4000b5100e101071203a500b185071000090701c40c1030200c1d11600204081c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 228953228 1250 228951978 228951991
    0x6100303030b0d020a06030c030605010e090a0203040c1203020c090906100302010f170a0b03010b01050304030c06051806070206060127030f0305160606030318060e121903020c0a0506041508 83
    0x40700c100013507901e252444005010641c0e011901304007a010040580710942d200506129a8604040f503a940d51103d11b5407044102c500161213698034180a2903142c00c90f4070115900003100d10581c1450307070200f103020302610141c50340050341c2c46440c1c0e1190358403000c4624602502c41402d051005605c01c0c404072050659600e0940c812850900280c603018000b5180340e0310b00c0b950307001c0b10301ea2070900f070107560744031842402d199045180684004d845802c2241c0f0050131155a000003031075002d02c2008141807203002c00200e95061a001101942c0c4110940710b080c0407860358881d040300c3c101c07801715003687c220415004c0c5d0500351955a032418400802901182442010300c210500d20f00e111888920280c0500f40114115155040c094050100e034802e0f480e0300d03c4079032000e0140c1d580107a9141c40c0e0b0748095030000304c00b80b01ca0000d5800c1c800c040089078183d1000f14011402d061740068200c0c040701c011207442c1090781d82d41c0d042101c0d520651140c04281c00303e500b03464890a0141d00055884070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 228954478 1250 228953228 228953239
    0x103051507030e0f0a12050406080c030c041d2401020c09190c0c0c090204151d0306130b010e0615070c030b01120605092a03030f181206100303030b 65
    0x103000481c80360804540b000c01144d00e030311065104040c00f0201079100240d441500300103140c103041c5803008003085401403c002132014004013003510140b04c401250001c0054040820074000b40e4000d0300b1100905a88035852403044060002c2c0c0040c81c01071041d80f646058004008d804076070824030081d50f070f00424213200c84036a4200c110251019008645908819980e12040c403041441c00303c00d01d40c825081004003a20620007442076810502070402c10002c2814005040b00580480013009008407000e140c0500a020a000c0394680c850000c081d014420390b13141c0c407a80e8840c05100e25010085440c80c0e030210400b00015071020704080200420b42c0034825100e03c0c1070322502d50201c0c0380f0081c0c4c0008526142e420f411f00c2448030500c40c1d25000803044c000307040308000e070308020086026802d06200d94008010030084050384e0410031a00c51081026666803580780e152105c0060310398005109000b2403040340c1c4811501070204403a4869212850f0300c020003802e60310308400903d101c0b2585a00036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 228955728 1250 228954478 228954491
    0x60c0602070203030a03020c0d0504030b010e0c07060c021f09020f0d08070b07171f15020127050c0108040f0b04060906090606090b060f12090c0a0305030c15010305150703 75
    0x143c0741400180351244d9a9180980d6806a0030340082c41c145840d200328003040000e000500001d5004840300b41180c03900024486151140340400040303224958006104c540b400c5200005184c010a945590500c0368a0f4004840f800c003446038191001c00800035404508182500d05c940703485950341e92150b018002180c14418190745210f10408180c500001041d00800d10b14114000c903d201c0da4400440c8030038110070b100c0005048002000c500a1080218102440406040c0b00b5400841591062101e0741801e041043d51800d0082860800fa180e82c081c080b65052154007540e031807401694004c0e83c40052030981e460f98445603002400c1220450b03141c201080104159010b0098034601440d00041c071a0724080340182150021100d290240d282408110140c180260079910205803050742c3d4060f030350b501c00e00141007284c0c0d403002c10780c0415155004014400000042d10700341c80e0344411280300c040d959010320f07182d07002440024617640c0960386452100c90098000b0381c001c88182004543c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 228956834 1106 228955728 228955733
    0x40c0f14040c020102190c0b010905060603070c061401090f0c02010e0318280312020703021302070204062c0f04030903021e0d0b07180b04060c060207 66
    0x52669400440302c454001e40454034108100c81c0900f4200900303440c0a041d2902e114410741d00f12203070100200b481c3e103d900c290350040100505203400d5640700c0c10100c07040c4410384005c80c0c082e51a100000c011214a640090181840f100d001c6200b003402ea500c0400c64062442c81c5045a062240800b91100040b084a034a250ba000301d00e0803100103030001c5403540c0c0143c4d42c0d0041d14541c2d0050219101c007a0f000d4502924403400c20118041041d0314101e941d0102ca0001a6002004c0c108107040110345034010300c4c0141c0b001c0c1c00852140e5440c02210310340e030702c503031000d070102800d009008281c3d0031000745071580007207041d04406007030401d40c80050440e892804001d000300d4607000040c17601d1510300141a96103000400919030001c0380c2c641112000e2040da074002c04520a0541c0746807180c000001c00c0191402d480c00b00c0d0505240240c00c0b10707124410749060707a400ea82040384101 = true := by decide +kernel

theorem cover : BRFrame.Cov 228776978 228956834 := by
  have h0 := BRFrame.cov_init 228776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 228776978 ≤ n) (h2 : n < 228956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
