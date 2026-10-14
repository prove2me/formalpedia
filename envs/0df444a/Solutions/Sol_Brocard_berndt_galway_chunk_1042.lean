-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1042
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:58:36.516438+00:00
-- url     : https://prove2.me/submissions/34a64ecc-5907-4474-895e-c7c079489760

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 187230215 ≤ n < 187410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 187231465 1250 187230215 187230221
    0x6140d1109130201081e040f030201020409060b27032802120d0206060105040b090d02040b090f01030606050303030c03071b0b07180503010c023304060b03010f05090c0f04 75
    0x20340685a41068200400c101c0c402d01c07940c00042c0c0c0881d1100d0040380c0440e0b52010041a403000385000f540b925251551041c4618100210603000c6640a20001c10124024800c0b0740003003801000140c0ea4920325261130812a0107244011281e403c804104807440d01c0c04144101c14404500d4045d141c0e4078410801d01f40c03400701502c060f4104000da04015582000010044504c2c01c0a03000ca41c043c0d601c04004444910590284c00310340b800c1405082c44130700f441d55680f01c060f03100502c0411213114107800304036021000c59074141c9000d11540104144000b610903c005480150051403031841d1042501d6a5403101074082c0042100491070a501585031a0359003110f0f0f54401d94564483c180303000001e00640c8401401c6151500c540c40000b0b8034501440f954481c0562a0054003100315080d810f2100c2d0303010100d0b4041050a40d0b0b10100c481c0340341e414440c1c801d52017100009440301040041c0360840b844081d030035a0881c502001c0c02081e05001900f11480300045805003407243c1500701240213 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 187232715 1250 187231465 187231493
    0xb030a020d05010902180f0105041e1203090611070b040506031315020c0c1c061e0905030d2702060a020f060a0905150c030114060c030a020c040b030106140d 69
    0x4030350b241600102e00c24482d81c00070f2044030504041e00040c005e843e0100107051200b15001c501283e0204402c20501d141040711610144111a4040071183e46501c0703a02410078a517021000a0461181482402c0d00041d01c4c1014050f980010003881d81031126000d042d12981c041c0911a9102100141c503009c010000708038641d45c8507134840704100344005134a002c0d4000f421002024050094480d10900741010710240383d4002c124ac0c07004840803501d650000788001003440022400c1901000080d403603601a990031540315100940d0f0f264203c3e0a8582180c03071203500c4040a400094000c500c8100000c80244081d4044a040f59a5000386030164079100180d4600803840c019001041642443c503071007180058022415100c2170310188801040c1201d044030301003a4031a0500042c0701c465584c1101040000c0003810051400d21060442495504429003500041c3e00c20b9583c50a0750805028407404403d098000748060341c1018201c0d51a60b51901060b8010b00000755000f00f8000c07443d2480b20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 187233965 1250 187232715 187232737
    0x110d12090c0b180a0815040b1e01030c0807050105040b1207091a0915030f0403031e0e0607092907060f090311011103010e0f060a030b130215070b010b030a02 69
    0x164451620700e0003c480001d003042c3c42c0c0309100100b0002a245c4000c070b22078a4001325012203200d1a50781c0d41d06d01285510140c110904c895403a190b05480290740c040130384c003940c0503001045049203090381c82e615010f41a0081c0f810004184810030590203401c0a80d4428ad02c18090f02ca41e95582e800212580543c80d440040744040001c0c1c0c10000c000c0c1400240700d04401a280caa421070180c8101003864402503400c0e005401d000000140401c1c4240e10186403021954400039500d080c1c240c0400c01c1c1e400e0407000300720541120080c403c4407600103100400400b5070f807860004165092500441d0300c61076007548103e0060000c0c09c2410041540c0c0000986040c040040120030a0703070800030407082c000f15181040750329010303840078401c1d050380c1031303a0485020f022003e10958801c1001d407081d10303020705419000003000ca0048001000c110206229001040c0741804214050041106641017811300b032030217031410041030020450050340e4a041d5034076011074079a00d0300c0d840d80c000028410b00000341 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 187235215 1250 187233965 187233967
    0x507150c021014040b04091103010645080d0915031d0106150f1b02010e04020c010e0d021608030901080415020c0109030e060306090109050601050d090f03110d12090c0b 74
    0x85000e810410146c8140c40c00b2500402c03041c42c0100324031910380b10a020300004913002050204008664120b810039440b403904004003240014880c6c030400b0042e140400f550f00340c041405001490707040060300a00100d41c41c2440b40700f4540310008407a40c2c1050700350400c041d21258a6061110187c5080302c07001c44080007000035550312822030b40b080100e080c8800c0021161005113000c2c0e4170517804a004160400d480108081a60380155802d45101c81c0725500b040c2c0030300460b20411801e101340c1946089043c003604003083c0c0d01c200241032111a10310100ba10343c2e11481401094400810386100050a09040c40706440d142001003109106140c074080e02400001c10742d103c4030040d04036070440e61081d1039104994012204020040c001141c85a401030040d500400c19800250000d030f0300050181483c61070884d10048510588101d21002d8580c201005507040c00c06601c000c80301c0180100030302601e03140341c4629004001406801c0071032521030300da05044081c40701c441c124500500c010450a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 187236465 1250 187235215 187235219
    0xc0605091f02030106020606190b1602040905010f0b0d0503040512120a02031911060708040804050607030206010519080a14010219181401051209012003040507150c02101404 76
    0x8800b961090007a40014081c040105065051030719841b5030122402c00300342401402d1450703695182d0030001d4115030748254000046c0158503548150801c6c58003074000440c4005c55210703d070094442c0b00e500b55002c0d440b1404034001084010064405551088508001107081c080c40da07031802450008901c00f1410020b00740b0003040e0000002c0c894044190f04036605509004000e44191000d82904101c54004a00141d00d0611480788654814414400c0c54185a22040451902e030009041140983e01140040c0194a469035410f0925040c40e103001c82d6a60400d00fa450b150308482000500032120f444440e182c040c0203406445002040e502110445000c0100c0117181300207600c90950700c40406500402d0f00075500120144070301040c6c4450349820050310818912605c02448004955038400501e00103455a11088103040203151840340c9070704044c103096042440c640e019543d080070074104100d02c5500a500c5c00e8219804590601030f48003c60300603100c0c003021b0000440c000c0c00010740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 187237715 1250 187236465 187236523
    0x604080610030309050105030717091c020a050601140a03030c030e030a030306060e010810060f0e031504140304140402070203150906070323010512071d04060f0203070c060509 77
    0x8901c04403406039071818403032035445006513143d22096a03502c0001c1c0700c030a9107450444083c00e070039400c500004110b41d41e008007124003103a0641c8801c41c410040e000900300c241030000800405002d4a00c45024421b05400e110025007842039034070008050018034141d803010f00d0b014015541c1d10b054040c065501e41415450024010311890080034040342480703507844420b500c40c40003184585585a405c480c0281020029500100040780c240c080255800e58017a584d1401d00402c0c0703c6540310038a02005040903e001c3d510303005403030566040d951042c48100101c0400710740259120f4420340700140c0c1d85883e0b0000c80e042003d040b04002350319500d0070521204103000103c0e5807013031a041c1c0d0b0030401c504042d40204039001c94402c443d85200100d00051000c0d02d4445a1040c207900c00c00129230700240d407020982a481c100311031604102c5003580422081c8041c3e0b01503005a80204c0b41d046203036190020f409062410701d4440070b0040d564035000200508000c100b050100000d03904890070391002101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 187238965 1250 187237715 187237741
    0x3080702121206150c210f042301021b0d080408061503010b0406053f0a03030f0203010e070e030106082a090702060f09010209130f060501091406070206040806 70
    0x10f80c103020302140c0f00d0350303131a00d120103007075440750400c8202600501200c02c40520b8081d00380f1201c00074000040000b180000d145000401c0100600c05170703208400e0395241101110f210100000e41550031800d041c0e00041840010b03800c00300760440786803d50340a6410581c1003401681c10250f114030424080c03002c0e900c0044032050503036100318000d00c0081388200070b1005580c002d101d2941c10402643c4911034852480c040c000c282850854982c001c03011034500d822010841003900e500a8203e6a071120502d0b50600458010b03821540c42546154500303d891400c0400040412003045091210015583d5003034218100030090380088400200d40c410004481c008003418440032f003000c0d00358451490422111071391045a072038010f41625650200641d4032208001c0c00035401d9582040000307a01d513200b031040303074421888400010b0600d04001a070310845109800040c1070200349041048114158900074000c050103580c420784544032071020594074000c6420001140c001e4104106203845205 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 187240215 1250 187238965 187238971
    0x804030f0506010603110d1d010510030b070302041401081b0a03060509180d0f050705070e0402030f0601081c02010917071e08071101230d1d0307030807021212 70
    0x41c080e00c036266a40c101c2070341215101007020600600138889004200c1980e88540920032410100c15008810300c060242105c908035200d00009011a40c14010f03c00300880082e80280b035810300714039103400e00134040c02c0460198240d5042103078040c00500e489031010442d50341d201e00d00d80141e446e90810300340640900841d008241c09469901c000441004000d00c180b40b000091101500410f10800c00844000384030401070811b0280800440c000100100a004010305008134250010304103071040604090f42420490180ea1000c0c0040c000b03c00041542c140c0341d9020421389c920034404082c1603014010128003e803882201c0d2241181c54034800008004561184c424128882c005a0740a000b20f4aa1000504051401d11020b40002e10380c800030007156070141400b084400e82071001e0404200c07030b00d403800e4440c50049400700c854076035030062215030107280b000c20548209039041a0f80e2030203803820103000c01c040c9901280b0300d103009001414840c00c1ca140542d654407001201c0b5003d84c0001c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 187241465 1250 187240215 187240223
    0x5070b0a06081b060d1d0304030501021207020d021b041104120c0b07050c011202090d1b0510020c0603100e090c1804020d02040c02011b09051e090a050c04030804030f 73
    0x20000f03400c0310b03200b94900c10940c6a4014001ea013010200d0109030010b1112400801d10a0300c0307103a081400c0350003003028100540c850000540d54110841180c400080050301c000300f5036100d45401d1451a401050740250080f0060010441e02803d000007405041000902500031703400140101d0403100a440d9449614003854541110540c3c1c0c4010b40214403448030044d02c260003012085d00e48d50b01c180e90b4070b202a40144009410400003a001944103440000200c030400d94144000e42c43d02d002900050003000b040300d2884a007081c00202039207a03010070403128410745000000460000e181034200020b4502e464801d101403800402c3e15030740e0706002100c070744074070303188450741a0169242550910552b40602a41d007281c410340d0030b2201800300011110159500e9185450a02180352000b807002d646550718103d0f15864907040c004003956a00c0000030841046071405c409441d5551000d4210120400020701b9030740d8507100e0203550242d9000100b0420b00040d00100348000e03091900307005405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 187242715 1250 187241465 187241473
    0x100311130e01260312130c230604081b0a080a0803071202090a0501030213090216020415050102031b120708031e0907060c0510110301080d020d02100c05070b0a0608 72
    0x104603008107400741d81c0f809490b40d036100700151140c450043c00b129801404800c40092080241d03502c8507031100043d0000d0188004500080c01c0e031402c6480d484421000543c3c52503c1e040c20104607944a171200440c4801d1981c14013000d444984401c04220001c000d00f0050f60740340c42c264908202154819107030280050301c40c2c6810380706078919208a406005c3d00401418005280070019001703904a0307030b2281c14007201d0f03d80002e0741c000d89000800702414142c1072048107416a1040004903980c007004428420850030b801d2000c0e907000401c03512a5000380d181e0514010f00703c1040c0703140c24401804000c0d46e02000c503580302006040720141d40180c1c1c1103d6464201c041070b80080104100403200070340d4552254508002440c06644075000450264041d03c001120044040c401d0740d40f54130b003022420360000010409e1000501c10041e41c80c90030b1010f001410300031800291380e09803148030304480300d0355400c0644a4600a00071101103503401407040d03c4510307105022030020b001d1441107070040e0103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 187243965 1250 187242715 187242749
    0x2030414070f030b0403021614010201150e060d02031c0804030e090405060a0203151203090307080a030c080904020c01180b070906020307060f06030206040305060105030c060405100311130e01 84
    0x1062078019585200704542c40039146403914491150060019401d40c000c21003452500001221400054003502500c070300d04104040009003103402a400d446941c81c2c2c484800d000389142140656001881220200341000071800020700f0700c1402d41443c40902907210000c80c41c40c2d08608640d116500a40303411000241d4a028040c946004850090075504a1000a544280c080d03001e150400f48030701204800c0100f000c0400c034022104007406c2880d80c07000c02c0030400c80c50104040340160a001c0c0180101c00d00561340070b041c14200641c01003a030040401d0200c0c0984039541540d00492124009005401c4640c49641150310102402d648600d06440000c120501654000d801c44101e980258600f001a44510006010040a900210751159000009030b540c400c0034001560040000c2c0181e94500000c1525240c04009031a01442e801d210400181d0346921420000d0700301030501241c030180a00c92242c1c42d10450080d95203100c100480810404c0009500a050b5a040c80030009000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 187245215 1250 187243965 187244003
    0x40914060d080a0c0309080d09090e030405060a050d021309020913020f0f031815090105060d1e02010c0206040b0403020306010b090d031805030d0e09060f011b0f0506070201020304 79
    0x58140d07031018044100402c0303d05040e9100d40c01c800d0481c2d00078a0076003000c584580881d8200819000c001e00041c40b601414080c47c03203140308e0064468a280000d40c640f91900010a44500494a085062080100c4d04180159913501100c03480c0f010740307007042d1505445c1c0c150744000f0740019020318020301084291034400e001610071540c070030302044207080c14405110102c0c282a8001400c0c801c404004060301c009203503082090501c440d0342d100950406290803407400c1e0840d0380c024982071181d480143d050300032402c0c40d203414070700c111241c084d0500306070b5600040c0d1f0620303003405009410100c00140090000c1d202d40181058900c200c0c2a58042c4e40d03603c01601043c020045503e0340800302c003901c0c100003401900d88013200200c2070540d065242d0f40e10f000038241a0500c14010109071400095801488e21151081d4006c0084812104608504000900f0000101c554100b0090072845103400d004000c00c1c0c0e170381c420340c0c0038003203456a00c0c00410080c080d400c01d58046508074071881c844c010311 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 187246465 1250 187245215 187245229
    0x80307111b01050405040b1c03081f050109054c02071d190c090f080609070b0315030102040329040b0a05150310050114030f03030c0a031104091406 65
    0x1c0740141c2d01d40341080e081030208002000c140021030b07400030f03eaa02d26800c030800d805c00501c038903000c1d0b154131005103401d241c00301410708400350940e01014080300a01c0142c0e0422403038400d85805503820802500c82c0d038a80b13a040d81d805410300ca15003401007a0140002c488050720500c0c503010380140b06c0300100340d05050f656903507170b401458080041ca15020b03000d0900103074940d074041b03014401c4802d400d40a0961004507005041a1000900240414011580c3e81c0c020b00c0014050003006046503c1c14008042d02e07619103010381860100c0000226065594001c409008564002e0085580700d9072840c0c0f0079401260b41490103424106000c02d0300d0305050b0b00c96039904c1990800900e0589564505400c4000d0400514030705103041407800700304090f18100031075688103550960020300ba50621515040c40705200c20540d100b9400104c0006100703402109890700504040c01003511842c0000c010f40c0600405041010b082c42c022070b00050b0803650341c001c0000342c80301403901c0c034290b210a0284038503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 187247715 1250 187246465 187246513
    0x606020304180902180a02070501140705090d051f090b090610060c0309121505180a03030e07050603070906030e01110f090a03050106060512060306040506040b040f08030711 76
    0x112100003902c8000080507500708008039440109144c0c0180f00d00c040800507481c0079130b800310ba07259010030f5020400000344646003410203030007080708440c6016800100a4404d81c14168081d99518944604100d000c00581c0160000c0c1240260f40c0e2030740c400b00d40010813900105030f4809038a180820f40202011540500030a40c4050624405003880c0050701c00300c1e00b0304022003c0100c070060005503944c40741e5140701903510541f01c1500c080107840e42103040d43d00c0905083c0c003804092401082071800040c03d4440680c0c9818086004a0b0041c085030070b00310780c0d42c01036030820000001c00003500d520107080d0068030740948003001200c202200803400c80380c1768140c0300e040744c2041111010071802036000d001144401090400d07080e441c2e3741c03101d003900ea06030300050100e07401282d003800040703080081661181058001707241e81c1c45c25880780ba80d110406031014204e4503816001c02c003445032158044400720382020f60660f590402800003420b40a8141250540b8003420a000340303459100613021070703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 187248965 1250 187247715 187247729
    0x30322090c02191a0c0a03150509060f0a090905033406051909030203190e0d0f0512040f0501110a111002010207150b0a051c06052e090606020304 64
    0x3c69a4920b40c46041d91840480d040d035007800d1000300401400d200c0c1e1342081c03048241e10105901c440000310050107585900800d501d18503803010061140f912240c00d8a54040070844000c108030b0031080c003040c1c1240a81c1c000c0c1382c0301da003403c04100038400c001000300150740c206114140c0300000a0401983da9035210302c1e20b5000002c480d10700012550b2a0401ca80103120f00d154103103a104801040c000b2a005c800703003100513810100f5500c0200c0180411900c0100182c20b001c1e283e440503a001841103a000d1340010190b800c0000c0307010a0102c1000301c4850358000e40c120310380e0703031f40c4030103080b52a818103104003400121455003540c0c2e079400206120131a951b111824000c0c01196008100840030b40030001d504640d070034000c03040402c1001500d02d0810701c414030f00060300024030080c4115a0040e03005180101000e003550300114400402101160307400501c0080c50b626401d102c246100301441080301c1182c11100303c0d070800340b10384c02c14404072110f44500300000796440b0000c1e81c03240282e10032a2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 187250215 1250 187248965 187248973
    0x509010512031903060e0f0907060c030207090903050412050f010f0e060402010c02030c210f010b031c051303050606040e0706090501140d050108060a0e120307030b0d02030322090c02 80
    0x3c00449030907454040701c00c850401140b81c07601c0394174050304104204c6030b002c0405084001c1c0211380134140112409440c862030401072100700c54401035503e41e8144038006220390b5907500c1000b41031284081d64085c2c01d03142901c42048176103040642d590445981040c415501c8d200c01030074208483d1081e801c83c1d503461000341180c2d6036960015a05101014000d0341c16005000016030700d580c4191a0a004144d2804501c0d0b80f80d0003107562a14040d00d04030712100d141c0c07400c4c5a440302542c0008d6005204000150034801d12081c545003191940100c460a03c00551048804410082c4c00b049252103030034140c0303040000c07400301c00c100780e56648180304400100381034003428005544103c2f00d40702e4841016032483c3c900250a0f10050889000f40d02603c3c058000c00207120359140d480c005c072811641c0840081c2400b0060200300320b000d10000d00002e0078036903114600844d9496280300b600f10300d0b03002006e40307403148600342242118801c410008070041040280201d04612903204000c03030204c0d90380c010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 187251465 1250 187250215 187250227
    0x203010605251a0405101d010509060103032a050304060302091305011802090d02030f0c0907020307080306120a020405090318061e03100e010305030406090b270103110f0301050901051203 82
    0x108140f0f02070416601c40c09a00c06417160314201d8083e442c0004014182c030b84402c3c04030310740c250071900302800c8008550810001040400d41c082220211085030b442c80940c1041d01100c4035800800180000f0080d00003c00c0015189406a014044d84d110544180304000c90740114030048074000d002e10301c0030341c442601000d01c0d41070f6503000d80044400134003110240603140d00000e00c0e001e4080344000556208203803103034250030718180751070704402140015801c7c94410340d54103400c0e0000030640750255545423400044008104081e44100d90040d1040090b400c1044906890354031901e00c03810340702c000055801141c144981165070f560000303900c0c62051002110b60018660001e00400007140c5000808038000c00710408081c021441407000759500e0303140a50150000c030b8258880ca100c80c2003440042c0b000641020b2001000c448810b4041c1024643c800690041443c030602003081d020104030240e03400000c1c0002c6059800032a0700a10320381c1c0e110200408403400303e200000b035030414814 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 187252715 1250 187251465 187251503
    0x4080424140a020c0a03050313060819110706050f0106020601120c0e0a110c0a021008010302030c012708070302120d05070b09010612061409160e0415020301060525 72
    0x5440090b01e41d1050b540b009500380d000030108400c40d00282c440307800024407201084aa50210001801c0c107080540c0f9603e81076140d06482e0020b000b8409146840b14800c0b0958015a411549181c0c2c1c050400c000504200030200c000c14024003450025101e03071000400d130400c918010010899000c60120000360405205188062014081c0d6040e581c4030804c02007604100d001030424090f46000820715032846004001145580391032042c2400100001400541c0f4003048106400c0e07400c1c04e02c43d00c1d06002450642c2d2002c400c03101e070304250820060126842201107044000c45c0e008440c0c0d00c0340340d0080c0101a44074403e0036844004203004209803000181943c40c1036512180c590000900a03545800c08a242000d0303071342c0ac8034019a2080391109062500180b540c21040f10002008180c011440160105985014601d80c0c402040006400c00200603013060310380005180541d1a5607503224081c1c6281c0007544403200b20380c074071684a02d0b841c0010b4084020960045035200010b075035241 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 187253965 1250 187252715 187252717
    0xb060111070b0d0e2b081e150901170705062802030705030301090c081806070c150c05030f01060e03030405130905120c010606050c0d030c0c0b0408042414 68
    0x40034070110307144c641c2002d03290028050001200c248a02d44800351000b40030000414a40c444a001403110000600a9000704042d0101460b4890070804a40e0313207804d0021862180803070003042e031202280d000880d81250074054049004041d000f102c5071a500c40b0304205007800750501211641914059074105400a07131001c4da010303082d40c0103403880c040d500d44400741164000d800c0244060b46900c050440c9036801600164000f0443e0802a204a00008a0f949520029009008018580c0101c0081c45644080200702d14a03041c010000b003028001c0c060a01d4104455082d0707900c0300c0d1000011400c3c000d840244100400038095032400f414a810400400d50f01c005031881540d6030300c585000520200400c0000000522003191110710001c1c0301400d6035040c2c0c1101f405c000c418400d0345102d0900040b0070007002d200382408205c1c0099400211158074540102502410600c8203200510405400400681d000003500c2c582140071511024805043c0c0341800f00094200e8110b1128081280 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 187255215 1250 187253965 187253977
    0x3122a0c0309010f0c0b1f080307020a06030c0e0405040605060108070906020601030f060e0d0903110a050901090b040209060a05030a0b12030a0c150c050904150b03010b0c07210b060111070b 83
    0x300f005c5c00e0401c4076850310350074031108440c8100400b00100c042600c840b00014107100a00c24000194a0078515602180032440c0602c100b030245a16400c00404040c01808046944003016108000354039090070210080c20741a1000d5001ca540000428501d52054220405541c1c0c40e400400c2d1691a6a8843c41201d511100c00d40e5055522011f0380350101d002e119001c1802e00940d0795a802c1400c0d41070410501ca4082c900038441c0031001030400c01a00c512822134112a21b4410000c5d44043e9000400c1c083c1c412045040d40c0b25000040e04032015410201a43c041c40c0302460801042c2940e800f405030b6000c0101500601e58414070401a81502c110310300c0407090321a917100d101e030400098016007070f00c40802c182130100d40d001c0384102c200d080130301c0b64200f055103074503c180031140307080300c050403e2006010700100d820700000c40c400104000c0003100010032512040d06844032024521115108048004031040b0000d000880c00c0ca40c800c41302d40344210b0a500203000f01e03d03e0051342808070343c40340c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 187256465 1250 187255215 187255217
    0x1090605041520070f02060a2303011d040f080310090f060509040f03020a120210050f1512070b030f04050c0103050610110c191721030903122a0c0309010f 68
    0x2206178500140c442030045d141c1e00c08252a0341d8040c3e0080d00c4603082c0790845070080309803400107000420400d201d610742894011851000d0344069243c6d4180f03d5104d60300054081c0804400200f40f1042d100031001200496a003d00100f001650380e02001082d54014480c0c154070403d05030100b000304440c4540d2001c22846401100d64142d10742d900c19454070880e040f001c0140c1c10071a02c10302c1d95451406042e0703000d8401c080e0340c5071600d40105155501c05090200320701480c041c869040a05c8801c0100101801c24405120349900d4030840300c030142c0c1c408840850b054001e803110305045500030f026841c0100c0700100000d4503403c0005003103038071007441504440503201d501000b1400b81c48104aa9400300c1680082280e03282c10940201a080006c1c00090990351014041503985184000b28000c40b107140075034155680c80f0034540c0b070b1035406840207a0036140d9152060211800c402028203202102944020300d0741c45400700307001100d00a4244038080390f00100001000d079031154254042d54011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 187257715 1250 187256465 187256483
    0x103050a0b0a0e0916030c1a070503040905060f030d0806010e060d02030112020301050f04030206070c03112d012025060506010e220b01050c0109060504152007 70
    0x500080d0819800390302c211800c40c2c0c0c071000e015020209000c24021040307640c688032051446c5030b460400520292103139595007504200c2e0a081c03020134400b2034207820340010032640c8654869481c50024541501e101d44148598108441c207400c01203594523a403241c544038110507503200001900c0200b0719012042d8040380400528807240a144041c1d4040c0880c0d000c0c0c000340400510515084503c0513140c0c0d03d140441c031b810040040d9001582030303800200391030a090507402500e8169800c0718440e00b031040700d000e000e5100101300e1285800014021501c1c10f040c0c26026142c4080c0d01f215450074102403070344013842c90040000f019030010b0010039030201e81d060055442c068601c46001645200f21141519101032052542c0d124032804e118200403a805200515141c9201c070260f4401c1207040012500c82c1da100c0c0c09a0b0091086e1001c00c815a0001d201d4003001c1d24007080140b108513800c9900e131104822210300d004c4244103200c112080e01c03039103203000c8451420014198010b10b0003102c1c0440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 187258965 1250 187257715 187257731
    0x73204020f0c060105040f0915020a120903050307031a030a0201031a030303010f1508070806122b080a0507050901081902070c090507030c091a09030106030506070f09030b0103020103050a 82
    0x4028401449104580342c00740802d54144010031050341c4121191100c4241001c0180000c1520740602c0321005030250780c0143d9412000b4401d5500c2400792180c0130440c0c1c0340a0051049c150032200461154006e0b5404021074000080d40c0400540840c90b5950141d011104c8600154040d0384020f641940e020042282c20208800280c40e65000b60444500000070010402c840202980c0040b0021028280b1107654a0710410041051000404540c46900306e4880a0745000382441a0408428404c84603032110340501c00c01441c42901c08a91400501004002602c0440740d110325401101e89a982c20f1404060800441c0c0596001d002019071000c0f20300c400d00030b06020f200074010325210364241c6062500e003071f20b0f80049a4000b0445024036007400c50a00380d1551104811051313036403030300480c0c1048000c8050a01140a40000d6540640ca00307440442481400140c041c85400d50340d8402d40b070742040f910116845001803000900c6260240010300043d03000b500255030040d104400010401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 187260215 1250 187258965 187258987
    0xa061d0a0e01060e1c1a04080d06081c08010312030207142a030a020d15090515090c0a06080f0a0209060a0905040506010302040305070e0403050f07031107320402 71
    0x1d81d082c0d00000204020142d541c0791420b203006100003002a41c0c500b03903119840c41d01d43c280d0f1000c1d80049a10f03c030600e034000504010040056402c180e520b045c003002883d0303d50741c10701d581d075889070202d070343c902003003203180004610038810107050740e6002040d5521414024410381c0a074201c031104845060320b9034145500d0400c00c103c0c1c8144034582c2c030340f240d00c04440c01400912003100c46000c030740a6003150510a0150f2603a602c00540071790300c080021114146400e02c50020280210010705a014001c428645401c24038152802800d126040d50581c034491801c20454800d284907a42c0420b00000c005426042c1e90300300198081e01c503107000352070030000c00c00080b140c1d84242d42c074101041c208801801541450b106490703000d0800e08003185060300355220166a004184907a41042c030800e40005e04040c0304000350b4149014190320261510007170f15019110300d150244441d05032094030300010703000710b5015506186105841902442d001d45c507007030b00080c0c071070100f000750019020050381c80300c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 187261465 1250 187260215 187260239
    0x9020c07030b131b0506220b070605040203010e0c152104080c150601020a020d0501021303050a1104140609100f06120f0b0a060804030c08030a0203150a061d0a 70
    0x3c83c025866108520303503628004120094081032443e40300040441488503031280d0080380c114000d4200d070811540c41c03920001c1340301c42d030a0300418501100410088104901030b0401c42c040d5200b14001c3c4203241c4a020032643c0c4150054400e03038805809440001d40420b180e00400d08006c01d0484541d64803284500454040d5050b1012102d0100000300b804000200780400e1300700c04c0308941d0305d4420b4108140002e64a1300640006071003000030320301c0c040c00c1040941c11107603016411111401d11599034240a52509280744040d00c0382c01b00c02140c1d400c285014842d20380c00c1600005000c04c1500c400080c03180700350300180701d10611010f90300c000c40c050340c10300803400081195075100007409450400450070b4030f00500c03030b0401e41410020300e09007684e00c2098002c1a41c05a19020f43e0f55a6141000c503030b03116a0714400361075611700105001040249400540c0314440101c0403034001610313002030003000c000e42e224040000b005810ba085980300b803803500c0c18441100034141c80550b601c1c3d071a240b581f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 187262715 1250 187261465 187261471
    0x50306010b070302011a21010e0d020717010c05070f2f01020c12100519021206150c120307020307060204090b0306010f1401030f11180a0b040b0409020c07030b 70
    0x360780d03010548070101075090080c20b60703140d882c04044c10640c0d000341c0403450301c0d620b000e44900f00b10011038020399041001d44c0050410104141103412100d0079081c040d440c0c608602030301303101444a0000081402c81402280411960740e07031828648800ca0721001d484450600d03003211017100c1c02c3c0c070342c0610940084004600a000c1300003018084401c0001a2518080a040d140901506e800c1400c58000200e61403200c0c000c5030a0100740c540c0d44600b200850100210803000d5144041408a1000412144039100304070076109840c0c101c80e0f0103800d42413801803156141e01503015103007a988640c5080040d40d0003200c2401100d0400c00c85680b180203907002500302442c20740e81e81c4600045481c04118403070040440381d0075500020700f0040c00110158640c00402c2c14191568016000d00c021a400410134080d05010b55443d5003081112002510b00d0070000c40c40340b049401d01080c140c805800301d40032505500b804a19262808601101070b400000b0304280d0341c024004000301040d400c61000384 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 187263965 1250 187262715 187262729
    0xc0501091109010f06020a1218030305220302030c100302040f120c06170403080903070b0a0f061a041208091005040e070c0201090e090a12031a0411070b0c0405030601 73
    0x10324074964010701048801c1684048081d180c08002040440d80202d08140340e15000103100003802c0807540c00740d582c010b560038100c55041002c24008245684603020340f40084004004a0320741044491220b201d181d0fa0001940c50b82000307241044074034040c05002c00506490601508003941c80034004c0c1c40c03e4551307001c0d10660b0311084090040006442124000d440345080003c40c80c00e0b40f00540a0055004200805200301d40300031442d002002c0094480c01607019140f40d01518020960a0180850141c44245a810074002065409102d1aa02c0d004424524501d085c07a15008000100590f601d1083d51885410001c0300d03625203880704c2041081400f034a42e540d40e240740807403108880200411203030411801442c1240140e0740300d1740913011140007088804e91a100c10a0460401d46895030003060402010441030304035402d44c02c03860003c0107030220080700004000502090b03070304c2c40f07481d04808101004404005005000d245810070140354000f0704060301d0b540071030320b03080c03080e04024 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 187265215 1250 187263965 187263983
    0x12070801020d090b060d03080402060f070605070c0501140609070315030c0e0402150405030d030c051209010b0f01021501050103020705150108060121030804060f021e0406090602030310050f010c050109 88
    0x1001e0003108084c0342c2d0020b034280c80401c51a0781c0368500400c1000c01900080c442c20000500d100c042010320141c0e0301ca83d0304100c0070041c90800d000d01030b060713140700d030000c903515401c040e07450711910300e00120355214080160141126070f82d9242c00710000c0044454501e60b0030010000800480e0b102e07040c40003e0b00b50f1062100d003908123401045101c030100203903d14080c0040000340304940b00450920701041c1d03503040204200304800c0c020f84040c091110078072192032004040100404054100f00c8c640c2c0d1041c2c5956105070380e50b000498a5459040c200141140c102004110075442540100843d40c000d50595002e0680c800000c100d8540030b82c030400311a40801c00603c844100d008010000510b4141c085060080d1a94090018400103001904041c1d4810040c180a90550119001d8440102c1c0000e4440001140340003540c0181c001c20380055000d1130b0218110f0300010440f4000c0d4a580f0680400310b02c0c00b02000061000c00018504200701c854054001503424003403402114450300b02c031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 187266465 1250 187265215 187265231
    0x1205010c030b03190206090103090803040c0f1a070b040f0f1101091d150a05040c09080c01020f190515070c141903111203070c1a010501080612070801020d 68
    0xc00340e81040c2e030014400d800140d65203111280001005203440d43c180c4869880310401001030f03005051a640207000a01e002080204000324080d4403c1131f55010441c0080c2652a003581050700c0c080e80c0100140d0b503204100480118000600b096400f170301c00c04801c4509002c960300d02d4a13000c0f0b03c200c101c03080c80140100e8440b540c1c0091081000e0801341103000e0420010030407008546402034090700484151049400c0c06440d0456140080c0a0240091008010b078081c0142100d50358400e900442c002d198851700698400302d40d241e2000c04070170003400401c4910700e107050031406800003245c0d80d10854400800075560708040621558580c2c0f6491f02003001400c3c100e03a04a43c0200e100c41c0b40c2c014200b2446070703040e61000c1c4116a80c1501c0c2021140c411076103864546440c504060b528020080204405558050321108856210742040fa0002c43e00c0c0c5064800280b0030b0044502117529440000c1d42410114a1038006a04c05021103200980e0380005c0c508aa120007001c2070f0203a210401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 187267715 1250 187266465 187266467
    0xa03080115080c071203090210020d0e120c220501062109030906050f04030602040b090a09020901140306041d0d0f090503030a050714071805070206090a02010305060a1205010c 77
    0x9000801c1840e03060a40841c42c001e02031500603c21180024680880110750420f0248242c0c0545161580038113502c21a000d4524065030320030040446000042c104000d000c1325007082e2540f402165640c1d00107014a00707841c02001540b80c1d55070091041c2c4207114000c003100c002c15005d400d0007000e651700c4420802c2c80d41180b0700142c54644000d41d01090400c950000000e83c0101c0c09001c6480528280e51901b00e6461716901600c10781d840035000030b0012070003140400c0448028010a503044440780d003020341c0c0301c8102050b4016221214040f54442503050035034600840155400f0300005e00000c0d241c503201109440140024458540c1c9500c0390700d03007a140a41103081908810f0482c1844140706207084000b0340c0da072092141c0041040408640e550405c4042411003440301d9003107065a0b0865118110482002d030700341000703c0075a00301004212030f64008034040340030760f48503009004100155001034002e0300000d0040354101d0074205000030900d42414941c02280c0c81000081900150544 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 187268965 1250 187267715 187267739
    0x120307180b0a17060d110d0609060b01110d050a0305060609040509010c020f070317070807080a0c030e120c150d0e01090506060a06051b100f09021327050106080a030801 74
    0x41c0c2d4407905500b0209003e055616808218600d9078462200c00c0c460b00c4c042e01040800411100040c208c80c10401010308206480d00515400d003001c0c0d039a5200b00d01420102680e40c0e9030a4a034602184082000404040c4680c02c01c644c4000003900c440d1600900700041003c40340c0444404a00da5500e10302840070740c0e4140059285109184000c3c46110b09540381c03103000700b4128051024601340001c02d0401c20040c20151000300303801400c500d03254000b01401070203d03a0111011070018007880840303c0301d40b40c15240842c0c5855140c0007816408806014492000c1101c907540003440b0303080c411400c0c00143d500400e40c034203420760004908191280b82451a1040140c4818491741c10301c2000d1110700e03030100039a03140f003241c0c2e95050fa807048000012410018642d080f030300b540d414818850103032503940d000840c2140c401c0e180000f411914191400851300084544490902180d0240001400d0b1914403071003d4081d000005156035540d00031850103042010480c0481d020030010407107400001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 187270215 1250 187268965 187268987
    0xf101101060506040b0a0e04091208100803031909060f020409020a081806041502040510080105030d08220813060e030f0109020609010f020c030607020304091d120307180b0a 76
    0x2954030f5051500380700c00c028160095440042c20807020141040c001d507950b4111900803600210f4003440006e0f4040001c2135902c080f1003180c0740d8458039500250b41c1c0000021a40b2400f03054511211640760070400700c0c0604100c800646400d0344650114803031050030320081c001410b40c510700503a101c03c5094068905507006002e5600c4a00300c424a0210202c0807030b0050303101303510058050303000b920214003000902880c1c01603600000c114901c1c50000e84c00100f02810386408404480c01003840881c00c4800781022035191405001126406171003220720b0044040b141c0c41911b01d9814080160010607080c00c43d03511880c00207070b020302100400d0905016101508454034000c0c8841407140d00400c030300f0b1080d010080d040207024a07000c100244240b000480c066002026a0000d0818902c000d41d07035001801800c81c401e141c80e11107545425059400c452080c09400035180700f83c16002c00c101eaa4000512081c20f1043d501d05600c0b501c81080010405005010081074855000840040146c010b070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 187271465 1250 187270215 187270219
    0x6040c15020f01050f0105040f3608040e01090e011a1212030a1a0a120b190f09060c030905100c03020c070602071409010e13060b13050105040e0d0504090b0f1011010605 74
    0x101b00b10f0842c41000b000c00c502b80d01160142184148101c50046904802c0030014101d103401003404944c6881c8070703401c94101c620459080c8000c10140340254202d0303426944007501440c0c0082c0390400c4e41000d5105d5070f0140d0400007074683c0c4140c8103000108a5004841c110070056584919500c1060440c5500c1a0080180d80c154012424031070b440310031b8445540040c1c805003102001400b403001c410f25860119680c0041401001070070440340c000740900080032286c01d400c1c5a80c1901982c880c2c0f08403525503030800014400c80e40c1c105012002000e550300d21908245c1c0070440042c060104200501c003c050a900418016180c400038500510011001034411070b0000010844510071250300ea4200f40311114203071140c0010700d40f24000382080840e0741d40051b0340b0040c200c00311105500950413030b402079505100c52454010390f5a211421481d2243c0032800922040c07100031081d0740413068010015040d031000082c0000040c640714995110400010080503030240310600c2030090800915017 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 187272715 1250 187271465 187271471
    0xe011505040312030f0b0a1508010830040305070303080106091a09120a061109040f0204080607120902060d020406030c0f05190512090601050109060206040c15020f01050f0105040f 79
    0x1c5907110f00c480d041c4100400101a1904280340f10254158011060070b04020071913a0580e80d9240349114149840d100d030340c04107003a8000000c01c0040030800602a000000451000c0e580100d560100843d0314035035031b002c5040502c070200016500304105070180d8000d4544000300c1d80340100007480d000d4030303820241c800080d045081001c10704800503690700d000200c0700203050b01e0352000c3d0145880c0903441c0c040e098034100f44001c0c41c2c1c20003010040c5481c4009540600540000d092404140e102c0e40c460040075a20801c0001c000302d12403e0328859400054401285842d42600010444d07000303c00c00280c070540c009010001036816100f005000c207400c0c01d22611070f0381c05c50800340440c091000040c002c401841200807801348034004481001c4010490316000d400c0c00d29500b036491100f405410301140c4502d00104500d400003800038461940283c02c4000c030f03800c0106880d48075160040c107009612801e503240882110a0003620700c0b6400100040745658900420807081e40c4080403003402640c6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 187273965 1250 187272715 187272719
    0x30b070c020a031211010f05011e030b011710050a0218010e0904080315060f040e0606030f010306020711091501031d0a06020a0c05030a050d0f0506030309040b030f070e01150504 78
    0x862541c82c03801c59401401c00c00e2030814524058921a0300d180b5007007415443e0503c40010212130f58882c42c183c0b0107004010100508154850560b9603590001a100a20b20f200400c06c0251110340da121490050080ea20220542500101550010348190398400d8000c1400440c140d590040d06440b4502480d12099442d82070000c59403040c000742000d04842000800551034010801c0c1088450394040c180541d20002e03101f174140300f6002400340031310f2910f200e07003c501c0034507240007940d000b03040110581500d41d1865272080e000350b020010840f41d081c0c0b9111040d009030380382228284159100303026620008103450006081700c1c00120104d8220005051224400c4000514690b0f80c40c1d201c44010303510701c1c5c50fa40607201156003503001041844005000c44001c0d0380103001d040c04d030640f074005009138029154048192141142c0068250f8010b02ca8440d4a14058002408691018003038a4401600184050401c030090300f200b2a0102604d004100d0340014020a008940741864000d0502d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 187275215 1250 187273965 187273969
    0x130f110108060d080a0c02040209100804020301150b37120e011b050d060b0a02030a020c0306011202060706091b081e060105091506130608100b1e070605090304030b070c02 75
    0x10090085c00c00c10480140a860210748490b4111400000014018010380702950402041380b81e040b2801c070300950a03c40c01c400300d5602610b40c4401d80740c942122a090070208010200f4000c280244007441200345241c00c840c40e003c00e004a8500501070307031070816034001d101400040e54044042c81d45140e1400b0784040000119680300c0d01580c0192030310341d40d904a41e5030124058a603540280510600016a07074000b1900007000f4401b0614540958585a0b03c030802c16032920070902c0340c0302640700e4446044006140c041c0c001c0030300381d00c90360700001c042c040c030b840c1c1e400007030303c1904252035803103d01005000b190301c02c100352292400720040790340c1403e00308101e40c1d843d040c041c402c0500a43d4804049240440c4a15680d90a4000a0700a0b5101c1c0300c200954107003500244982c2c4046844440454003482522402c00140d80748050300030b18108104210403040c0a000b002d080d1a01010b01c540d10010311980500c9004190a0004640321760541c107148000c02c0c0052b20f20320911031289c641c0b40060b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 187276465 1250 187275215 187275217
    0xe1b06090411040510030207020a0e0108060109021b120a0314130b0403020a0503070501020d0c050a080f10050a0902040503240c03040f080c0106030b060d031403130f110108060d08 79
    0x5001d45000c01c4000c1d1807055140e09000e50340019178401140f03596580c141d139065019209042c021110889111b40d102c0050010b2039081c020851150000401804008420b80042102843d10244078041301a650451030410842c0d50b2079450302d90001868804a039454049c2203032881c03c0441d0440c80e810007880f030303041c08e0b4664003009000310b04510004e000e040c0207000c901a2203422400707890b9101604d1070098001c1d440511810101442e04000e401c141c2d04c00c8058401514068450900b0b9444080c0e10354040d601c0203200500340071a980d80800c2c3c584880b0450401000842070240e150750500d01010704100005d00c13880d03003001c04041c0001c240c860b54007226401555191425640341c41d0ba0500782c02c000052940074160800008145d900340320305500460071030340140e070024001c1d241c4404100c141c10a0801c0580040c81032a4820401841c00f002103820000c500c0c020000d004040d55640300c0c10314402806e03211000f442c81c19004558005c1c140f95804601290900003054542d6035107145 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 187277715 1250 187276465 187276477
    0xb0619050d020d080f0f030a050c030103150e1e01050114030c010207091116050c010e01030506030c0103150801050c130f0605030f040609020a080706110d14030c04180e1b06 76
    0x210b9000941c403041800001c000302e9034400c84c000d000c0c9035200051425804141c0c025100c294810f4684030000c0c2c00cac00d0744070065a06076a0301c50001c2d05004a1031401002625001100344c229010394814454104034803a0010360f00000c804c00030400f903150460089201030200c40e03641c005c3d041200000e440f0ba038040303140d00503581d4003c00000e64442141820043d400390100300c500502090051400380440012000314030f0ac002d81e00e125180b07a04078011011780b202a600c691701544226070014140d8001e800011a802061098501b0305036229480c50070356400741d0b0b12400241e000161104040300c011000c0020380613a031214440c40345000401896440010300902c01500b640001c1000c014258004140f142e4009040c214040c0c0c98088154403103005202d0000442c1118404500d51280070038003102c08402515111902905a014183d080d03100074020003005c8010032001c541007103000304111307048546400018816a84408142c50600b01c1501d020181c014543c902d12603a440b1070450311 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 187278965 1250 187277715 187277719
    0xc090c0905150d091406060a0b090609010c05030d0203011e06020307030807020f0a080d0609060f03082107020a12080f0a0b0409060e0c0103140705031f09090b0619050d02 75
    0x1482c0001000030400e5801440203a806075814040c0300000d000d06065036102c0303510340c4000e6408580350704041008040141c1310b001d1840c01c090000c605103280c114050944e408060500150f504050b603101810741d8040b0f82c04490156000c80180070781d020504920038100c100e9450700f62000d09000c0003959a002d0000001e0401088000040b2181d2090240c0000c0031100022601900710038078040c03c2c15081820381018051808000040c200c4207801404212902140407039400c50554540355a00c3e031010344050040c01e415140141c04c50800065284600801d5014000400051610810801e10310f1602e80821007940240141460f1a50015410604203240040e000e0a0b02c404240074002002c0040c000030b1074401d10900300000403498001c0d40509a8080049441041000d00405c100341d030350ac80025400d000080ea5040038244403d514002480640481a510740400050b070340c89500407142c1c28855424400e036030402070000b02240a4060000e0a494100004108103660488004c0c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 187280215 1250 187278965 187278979
    0x612030f070609080d06031e0819051c0614010f080a0e1c031512080403060908040911070201020f010c170c070b0c0c0c09131104060b0a0c0c090c0905 66
    0x10000d035a408400d003a50b04c500d8113920b412126600704014611840b056a41c00708640501c4100d441c1c0c00020010076a00911146c100b56004410b0182e200c0d42c03884c05000c0c400c0401011001d125413000400601c062000c02260003414a002c1503d00c0070415040b60603c010349180c4000e203500075800d107512401c4840c000400c4100035408900d403400b081c0d29003036071000260690380080e60580111041c0c3c0007200454284035602d11f4202480014004c010300110010310040c40000c406800500b83da40c0240b504608103521025154112a00da549001d0703c0da60000700c038811560140981c0d62281010002004400c001d40400b51280c3c40110448000d1600c1400150201000c0303000d40b898030b90008181c07440d52500d50126100755010030b007074040500c20391015040380d15181071090b1207002c0c0c14142c481c4801e20342d9540c16048004825240d40f068a40101055484258018043c500b10990720a580c1c08568141415812a50303040010614101180302c4050754006014204840c400d40c0e031a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 187281465 1250 187280215 187280227
    0x6050603270a1403040608060306160f0201020d06090c080609060603060f010c0606080a1b0602030d0506030a05151b040807050f030307050d05090111060f0a1113031a0612030f 77
    0x141012482d000050121520020841c000c610000243c01680c2540d00d4200e00c94555104250b61010121901c00c1e1039001c080c0c1e0703000001c5c4505040d0804420b18000527080c07000d48892001681c9d410b0308003009040e0342c1d40300e885000354400c00707054111205883d020b43c00c9c10715502066441c880282442d009620010b5082002d0340302e04401c1200c207421000030402c5a0f26407044540794600b80405071550300712094402002c0320b0718170001040f90342c950021841d180034a2540005007600802c00c65150003200000e901059003030000981c00c04c0c442c01190030034509000450b002c041654500156003105100510600000207028415203500300c1d070700d550f04040c04000900d14032840b10700820b00d00508050b4581c013500302d0054100900240c03110016480400076030f9036581c80490b06100180c03540c0d0085403208800b03a221030703814440b18021902e0b0000c21041c2c003020301c8244d40211100015007812564440c06c2d140b8041e00050102d5101481c00030f8407500e242d0324080e510030864151000641 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 187282715 1250 187281465 187281541
    0x31006030b03031c090c0816141507030e030f0106050307050405100b0a030f11030402091602070b0c0309180606030123040603061a0405010602120d0e06010b0d06050603 74
    0x1351504810402d081c4412603000e200e00c800034003c0090103ca148075000d002050500001c00c165200040e0100b07402e2800b480c1000b0780091108c0071949036003058105209221400d80360006242c920b00a880d000e12008a403010300d8a00030500a840c0b4281e45000c60038040750754042117405c2250340480e404103603521585c1c01c072881c444c0c07a41c0c400c00000b80001404000e80ea05074004000034140c3c0d81003005640558003884a8520040b00c00940c0864001d0004824000e04001450b40380343c244120703200c5c1a210440969254442411682d45a06c00b003060489847e1211003400da0411002100504d42050b01c00b08460380010700604002d66442c4054000d5402c80d4071100c0b55220000b00300340202c580d642440030090040c840000039a80f03c201030342c4682e00303081c0982c5040382d00d00c0d401042d2454820400b84c0440d08501101001c0f503455441d5890051b40407c901c3d4003034040a0790303241d518114408100d0465060354000c40c068042030003048504880540308a00e50361340000c890b0f2032135002c560 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 187283965 1250 187282715 187282717
    0xa1d120406230c1006050904020a0504090f02030d1805060712080c0906040f330f050702040e06011805071b080d060303030203160309110f1230031006030b0303 70
    0x2d00c0000d156400708a8441da00c100284a031854070070181c00300141502c0d88140b003652803003204c01941110800760100182d00f080da00010301180110100d25041b45240c0c002030902c170140300300400040c1030b10032064002902c0603034400200012100300c1e11b01041655a04400155403100c0c009000a000001d000e000c02e50003207420f14140105140e0392241c54070200000c03c01c5501500c00c148003100102079540031180c0d0b46402c0200300b4502ca1884004215080b215400201c0320541044001d01c903480050f140c60050507440f8810802600240d81070284912002135040b84040042e4140300602002d01e4101c80e041c079812580640c8428030f03440034140f04400d03208203140110400d103044000414141e00d0b9010354010a8005020031b0300c020300110460540d002020302515074143d41780711070341d00c0c076040381c490b03045040150240c03480c07100d103600c05401c1001c1d210081740310602085c4045040800d030301c820480c504e1818100d90440c00c0411688400070081d0184c00c084c5540c9024040e203549d0200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 187285215 1250 187283965 187284017
    0x302150d050703060906060e0112050c040308030c03010512030703171003050f0a0c050d031202130e07021023040b0408040513020c0d02030708030c0315090a1d120406 73
    0x1100600150030b0800d4010000d11107031168809044c60640040f6006124108041c030707d4005030b4482907805005017005004020281206010040401000001806070006140709000c80c0426a40f0780d8034140500c94410f4060b403c44c4400d4008114910010f50452403d43c08502141491450b13030352410120081c0501e9500050a14130410000003441030b40090301c00b00252042c60305444096070789090241085e6051002004905014185008224103034003811184401c803001110580d03a403200e40c01100b900356141e03c0141c10001141605501d18007a22100e441e005a074203010300d0443c08203103a01d03070300500020704507040503000c642404404070969010b00380040560820082c007240c01c0d0000d5210080401c0c450050070502a00680040156a100c40c0c118845a10359a200881d80c081e55000414503140403600c54581c0304240c0b120f46200d07100e0603403880006040800c0a543c00114803d03080c881c0c0d619402a10550458a81c1009a60403100581840d07100100b004110619109181c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 187286465 1250 187285215 187285237
    0xf2812081b2d101109060705070506070f060501050f06030a0203090a1b030c1401020703230106060305061f120207030903081908090c03030a1d04110307110c0307030215 74
    0x181041c0c0000040b803003201c18040040011030f2400301440d200c036010740f0103007000100708440c203005650582c20308000510581e80b10720281c030000f43d159000185aa00600740949003495602107000c00c0101e144503480c0945011030766404204800c1002606601c0014031222181e50040041070115000308041410154406040d00e1081c00300591b41040502c54030040c0c41015480000040607400140d00c2c0d000048103901601c60581140c0300c03a00030f0310803803c08000c1041c1ea403500f410040428071600c00600701681e008070352403e00380d0401000c02d80c6042c54800080f107520000c00f44c15002141a0760034a07061a0140c0c6900b0f80342410317078030121a07520140060314000351070b01d01a0081c0500b10068580b41e00c0308142a1511004140d880010300c240a82607807080003481c40150103480055502410b141c0300d2064006481c0214058074405a8100c07583c420200030312030300a4024030b000340b05841000c01450302e5041e410001e6030343d200360302c80a8041c0e61040d09100501742c03914201c0300ca230984 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 187287715 1250 187286465 187286503
    0x90b0304150b0a06030b01030b12120f12090c0a06170604051e041203050907080a020607060b03010216020406080c0a0b03060609090405101b0f0e0f2812081b 69
    0x298140107000340488071b107440d0009150602250b140e10380103240b1000394540c94000c180402d030700410800c40e503000300b2910070903c10138410500e040c80d006520311300c140d0340100905000c800c10300c00e02c0f000003401e4002d8014003240d41140c0e014a901280a194406001c03500841c094950800e202800e4038514007101c50340d581c2408100034018580344200146c41036640c104040d40e100d10000d43c440c1200d002c2c1c0300702600319007280700140c50024007030311000b4068980001d00d100d00c40002800caa1009541890900014a120b401e6140c24400c1a00801d0100b0107000e201000e03900007010031029014a01030584040302003881501c541e01030790280742000d072102c1c803903080c00c0c100181e690070070a081190060428603098050310401c0030880040500d506d4aa00e10320141c20140c2c1c04031005084540c1018014581001c90b42c0c85100701483c61001c07040e801c000c0014100981c0c0b540c0e0803600424082c3d00b00398190000158a01c049488100200030090030340341e0009506400c1c5021300071001c0d0300d441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 187288965 1250 187287715 187287719
    0x2040602010209120102090105040e06040b090112060f02090a090f0b0d08030a050604020403030c03050306011116031505010609050105070f020402040f14010212090d050307080c060f07090b0304150b0a 88
    0x140542c0102060301007200c4844030703502030403d128241e20941c40301c980011400e01080040c413207450b803500e800080c000c1010a001100f2000700d420301e8804d900c614000d60700c03442040300b80500f41c45071250900c02e90341e0641c60240302402151440385c46110f800c401a541c3d0a200e03040101d240d110452610008001500700d42885c1030195003600107880c9115502c2c5004081011460a807003100c1c01c507a4143c4500714003a86544064440390401083c035070502444189a0711601014445056810315034501c020b10340b421400c01c0010703080d155900a02003454800140513144d0056030798001c0310070900e85966901d8261500208440302003500a40017400440c0100e0003440103410001a03031704440305080729070580c40049a448519001c00c501c8410104100301282c02c0c104881c150250044040300e1030503440d0780d1480700c80d43c0b01e40040b0b007103504000c0521111070381a5040c2da4220019140050701c0303d0407d4529040c1e4400607100605842c440c51201003940d1841c1c100425241000f4185440300ea = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 187290215 1250 187288965 187288967
    0x1b02030705070b070308070c050f15070e010306031502071e030e15130b0a050708030c19020a0b0a051801140a060b0418020a020118050c0a17030307080406060801020406 74
    0x600030110403500d41c002c0080104003e02e14600340c900d00354055079400201d07100d01c3e006550340d4000003002d4446014141401040000401c180c5c4038078010b900055405140c029001010072002e5507a2904150408904102040340c000135101c5041815000581d900c3d5949440032010340080c022102070a180d02c10003081c140c01c070315003103003091040c2c0d0fa415031800f070382e2000101d52280d100d0130f040303d0030181c030113111000d070a50182809400d10b040c11850000961a00901500102c07998800303410300084101d0058101e460742d00c526a42030005016039070342941e8204403008014440c0260f1940c0b6400540040301c42e2550002000001008000c20f0410164402414004a455400c0e4505240780024899001c03000c0703800322111000c400c0c0c00d2010a24001e0069444000010215074948204030b241c95000b642100500e07200e10014009549284144021080300c4c0d0300403034210708603089000c0b01803000300440360300c521035141c00d04895075545801c500401c1a0381040625601c0814046445 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 187291465 1250 187290215 187290217
    0x3071707051f06060e061602010504090f061a1204080306030111040306050f1f03020415030206040e07020f010902101107080d050a08010b1602060d02120f06040b0906100e041b0203 79
    0x444410401482155101c0c0c2c001c0d552a0170500075075421110400c001d00060102c01d10307407400c4034414900245400d5861a04205480369000854030f00740d42d8800801c403040542000360301e0305101c036480500b04555070a001000c14401400600501d0b1300000040c07440c3d50070f51104007800d0203800c420b0740302c0740c0b0b90504000030704049446809500c0301c20b01242094a04100c00342c0244540002d0040755400c640c02e000c060080510070303640e080000d4001000507920b50000d0030180a416032041018900210001d1818400c4d60040e0900d0345807862120158840103039804031a101d5003806180403003c0c2403918600742550b4043d9200e4004c10751000360301c66025008000040b00d80da207040090742c999400040d2440344d010010b50101102e240d81c0018100303c0003400b01d0017003207640141401c40386841c0780030b0414100c8200c10b800d03828100b004400c0ca46807103800c42c6400d050f2210f0602e4075005002c50341c11015008144248100702c20b41042036074480c2c1084408401d8010320b500b00e00908038001c0c0da6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 187292715 1250 187291465 187291513
    0x2c071701090605280b220f0603060c120207080412020d06050403050405272e030f0b010e0402030c040b0d080403051605011e0309080c03030702150a09050307170705 72
    0x2000865082c4084a166006031040d0174801400884411390002031144040251400c40d070009440f010034100c28501032041500442c005d80022808494544004010b0205080e2400c48a84140040c002160068041da800d0704d09406203044800300313030700004a05c80e4201c400200813505000821007007607402000303001120b10645009003440c886c60b08000b003c4500c801246020b001703800025288203000e031210800c00c1a410b803c10a07608501b9104460142141c00680f0340741003e109010800c81c55810060040a03180240350983c00c0c503500098940340c90b41b0099218035100c042c00280307035560125400944d40d0204080e130740d0300d91307900e410358650340036030501c1081ca0034094001513a540034503002401c0d400d29001ca444480c91001d402d074001c040211060301c0302c20062004100c0c0340000c00045000f00841d030024210344129502100400c2002054150b0306410400103d0000d1030003c00c1e242200c0d8009250701c20300e5420f441e0038049015818003d4818440c44918100708102d0b11381a1342 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 187293965 1250 187292715 187292761
    0x15050a0503070608040b060a08070803130501050307021b13180b06040b03030313110a0308090306010f060905060d0e06040831060c15050108012c071701090605 70
    0x1105503840301015240e22491150002040384080014001200710820710361218008100909942d221540f2510341010b58100300000e5000140c1c0c44c44e00c04001010700014002403030803510318508510000c1d115040da400e04101c46c08990000c42070380e0394440060001c014030020400c14080410326620406d41d031030105032803845480303000c5652410300340100d06107401c002d4021461a01c4c0e003000c0c0381c902c000601d03041c2c594081c80c0d0640d64465803070004010043d8043c0316000e4507040c1401c109410680d060340310b00c03010b908034041004120b4012001100b144d400b29134140d12800740303020650180c20180181502806104100003c0040e08006007001660502003203940914241e4442005040e000d402c1c5682d58482c0400c00819114102043c40c0d24400c80c46d030803006040b2110042615000c3c4c0090080380d4580c0e41070844112400b001c881034078401d4010800103529884d03d90303100c0c2c8140c000e1243e503442b0b030700010222010075080074012591100e0704002d40e10b0708090f005550416000010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 187295215 1250 187293965 187293979
    0xd0b040203070f14071e03030609020d05041208041502090102070302030109060912030501051e030102120412020c03060f1b04080304060509040e0607090b0d0f0e0706080f1909151505 80
    0x606160301310b005581010303034000149000049201000c000c1440907031421010103403a800046040c08143c005050b51070080c07000071a2074205860541400d26070140244208138a020410001c2007510308151010300c1403810059880b07040e400100d0806070940c1001c1c1d0150309082e104420400594840d5040b0741c01041c2c1c0500c0110214003c41c1500c07428880d00c1c3d032081a15000b40d510803002141c3c108601c0c0000c0005107080410680f0b0728481c40c00701e074292035007d08040100407440c3c0502a0601100c000c401511a61400c0d64081314080000340441c6500381d4800100f220010250341220003500c0410111381c5c4880e80d138003000b08683e2120407650300a50405601240d030b0000002c0303950140050741c0b5196096404e0480c1c04000360000c1c070004c0c4901d5250b16050010b46400d01c2200040c440d0740000c2c00b403c80c00c00c0c2c00600511070113400002910602d40401461000170030010203215607412010500000302d007000c120742d4221840c6514124504520440c2484c10000024200d420070303034002e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 187296465 1250 187295215 187295237
    0xf1505060a0609050f0109031505190209010504210b0127020408100f02190c060c23030c040e0f090f010b031b040603080f03040c08120f0d0b040203070f 67
    0x40101007030203104410102d442060140407600d420820220f0120042c90800e440750780c0c94845514005103d0705680405584000b40051050b01c0d105a030b0000001009c198034022441c0c0c0001c05520580c41018500304042a81c61020483c4c60141c41ca819005500c00d002c5503100d03d000899508a084030070580c146642404042d00303068000d0750201d0f00c0300001741801c420ba03440c000c0301820850640c41080c903402c01c608030440d03c040e200050104895580e601c103403012841d01c00216550005520b0a012800c06a00c552001e0015810818042e00107040d0710f80c0c40301d10030244540a0b5804c00700f40410f2104c10420b45082901826224207a9001141d00280700011001d0803510315045840c4c040d041004100c200c01150f010300d107403140006d4000540c40c0d90b207494150310794011038000071810b0f034004180014421107099010245c00d9140240004400c8001c40400324405c12013284a50000410500840c410a0380700880030203002d0010355803442c020070010b01e00c00c0c4401701c180110390b000080e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 187297715 1250 187296465 187296469
    0x503030a140610051e180307050604050d0f0f0f11280504090507050307030506011802030610120917030117070803041a07050a0602040f0611060f090a0f150506 70
    0x961030242c0b030083c1c02c10749900d6403100220b655611409442e00c20b00e045201c0207a072140000c0080c0b405001144410341200741c40410503007800000d500c86407160300305000c2401169101d011046046621011010301500d481c5099000d04000c450091f220703034901c440c040c050186501105011140840c8e01d02c03003829036016400746182221100310421b10781c0740400e1005003800e62000c07142078000c500720b0b03c24603581c0300040c1c500100740c3c00444030368005070010000011240058424075a40c12010760451505402041e0204194100f4208000c1c440c14814100901d03540301841007600038403160009071242400404d035610170702c540c01d0300021104280700385c800045076480540d50b8445c080d524007850701c41030f0408035080c81105001c1e004200300c035500080b070400006031201d01c01c51025864a01d454540140c8544961040e418800b500303401d0100f040b00130031141c0e8013114400255880d526106000ba1600034140340042400092045100910139581c198281030078100006024665810007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 187298965 1250 187297715 187297751
    0xf0c17030f0609040c05121002030901061e03080702011b02030316110f0a1406220612020c1509121c0507030b030a14011404030c02120c0a14040b0d0503030a 69
    0x44c003c1c0c107142c2da2800910251900e482d9074004600b8020484112990300340300c0204030781c400e0302c0942150303548490410030401d44800184509040060402c035551441e10744204078070550b1402410070054446406985d01010340b01c0c5401900542143e40342d400e1442110047c0150110607500911080f040311003030b203400d800790280004c026244038402440c214003610040c1000c20701a0384848144250b0f51044880004104003401d0f140c02c20080c01e140c008081e03d50341c00402c01c01500340c010004c08090356000a598400c45682b075420030b41c1d5a4405004034206180200c140700605d070001505945020040c40100350101d030900104a540c480d094240c044481420200ea0542c10040403000411241062501c0c16081207002094190b46004224207150f001c440480100c1c080050b20070079402c00500e51010000d040b0010540301030190000340c04440035101d84481d520400d80840481d8a8a810095945001178240620444075182041d200d070000c0300e090611502e030a010011003203403c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 187300215 1250 187298965 187298971
    0x121218080c0409020d020402030702160b1812010e0d030609060b07050606090a20120a0509030412111003050123090708040f0c060203130b07080a0f0c17030f0609 71
    0x1402403a4014408040c040940074000f07040c0da2002c0b03a01603090150300c450008500ca0044c95003e070683c0c05400c0e03e04c0c4ea900d50b1030f4100b0034903548140212000010080300308881100220f03001d03080b40c020341e954240949407103d04540c5c0c600075500702e199505d406800946c15114181b2081c04031f00d40710000490180261440600103a0125000c52521f0400e243d007075422444105000c0780408881d00c202010421110054000c100000364a40504281c102640d800c001440c406022504003031203800e55901850084c15242d07000403503c40304118904c41c42800c10f0034050310407500c6402d000c1c0043d008050900c038032b1504542124640500c07401508210052520050000c503031629000003c5514601c0127204403001421248558041005599403400038045a402181c3e108184001e040c41c000d40382d03200c003081003010700c68180011011030a87d421080d19190a107140c1805c07050071544940d0300388002c0d0042003441c001184949001004501c148841c440709942a03c419040c071501c50021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 187301465 1250 187300215 187300229
    0xe0604060506160f170a050403030e0f0f010e04020c1c260c091507050105061f120203041115040e0c04050f0d06021b010207210507060b0109121218 65
    0x10110000841da1300c540461079000b0507aa5040305482c1a1003500b07a07110b4903101001c5140400c0070020940c0c40200114013000c1a02c01da0101d44449005c40c406a03030349600c10781884030540f54000951115415180c07014000e20481c1d245148990030f42191f040c21a0700240060010203156507200090080b0350040351001e07000106555529002e00c0240d080880079030380c0200242c51a075040c104050240c02c619001e60000501400e00008000806e400a4000c5010204680309804c074903802500c80303405543c4000e00541daa07922031074140903c49820f00f03c0c56001300d41081503c041ca0524020700155615a44162603d40710f508252140d40590f10a141d0f0041e0100c081a501d0700b40078400301c9040f0f00c510400742c1841016907808542034400300264440740c0d40407036907400b80008040b06032485034102250401d00c4008200042c2103102c0c0000c0502038036161902ca101c5640b243c050a8001d10104031640c042400b0f030315200142883e10082d42000420030800309002494000c0315100325161 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 187302715 1250 187301465 187301497
    0x30a0c120306080d0e030a020405010902130806100501030b0402040806010609150216050d0201021507050903060a05040b0624030112060518100b01051c0509060a090510050c0706060e0604060506 85
    0x80d04c110385c4032451001994140c060708051400585850040e02e002e440d070b1140140c0c1700c1003251003040f8000500c1e802014180d000e44103014160034100fa130030064410070f00e00858003100442c007141c064412540801e42a100c2e80d8000903040c0e602c0081001955810030a007440140d040741d003240e99610007500000300941aa00030040c5141540040d0701003403041c010388a1001c4a0700d55042804c2e4111100000704800080340c445620381071002c0d9500c2503250100300701a00346602d44a6000b032000700f49500440c10002004c684003200366908079502031140f20031742e696031515036081d2403124600c411184a0b0800d80400d4140c90684c4410305500004001000480c84211880014100c91840750341404010040000403010039009594441264403000c915402c0c0103c20514002004180c03007806850500034100040e030128074800b09040c941340c08a0982c440c101020303624031592400030611850181d00181300e400d401c0015100312801c540800c5807550728824040030f4032525071403c1f030740c0070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 187303965 1250 187302715 187302733
    0xc0702010906080924270309010809070f450c03060801020f040503160e040219050d030305150d03020a080a050c07030803010810091121030a0c12030608 67
    0x8415840c3c0d80d4001c101340d040303610f81002c25600b0780003950b0007901820000042d00c100090403088980404500302c18a80050b07028140c070400ca500c03406000401810014a140403a003100d00c100819005040d040c1007080c8503035680c00b61000414000700800e411015145802a07188010130080b178640c030500e4085210b00c001c609616002064007d80610a041d5101000720300800244040c241d80300c2000c02d00740d6204d081c03a041614007101d446030740703404120050061090035007208484c0c1d0015410348500d0184000407992201d1601a0740060350820b415070402418554150010b5020311161054804490009018000e0348001003501401503400b005071400007607c6a0f0060860301450300e003141c10944103a101c03500300090350780306403007000002c80140064070042c482500329844240c030810017100707195200180e440003160070038410034010008801c081c0c2111a6290404424010340e50703240c80940e00a03005031a4107105a580c0c0c9100001540e00c07601900c01e450507961918002d2002407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 187305215 1250 187303965 187303967
    0x50f0606161509140105090d0c0f03030f0c030b0a06090812071416090b03010207030e091009061e080a08090d150501030b06100905011209080702060705010905060c0702010906 77
    0x10a103841c1129a24008600b00e01c2d10350b02e920441c416a032180d0040e00840c0300344200c9030309413100500616640d0700540c2c411810303160840040303000d040d131110030907070031040c24141640203148827030200c82698101011800b1503941a4021401c3d10402c84144201e603480e00800c075007440090080319034680c0000e654001c40c0700510090f210852140c200b103c121100c604405040c1104c0036051614118100410f00603441b5078068155050741c150002c5040901e151001042c50003a0381416018220740350202d08a00b00072071992003c1d0440c9682484417599511001d5040d03000e041c10074022007501c8001240b81da0010410200d11900320300c0c1c007400c021485040218400601404030380c150140c0c09402203103029806254002c41c050f940002d0079182900504c0040c803030310030b55a030400c17407952402d000d980e80080c0c00300c203516401d200010311301d000c91408515910400e90040e42c04800464010200101500080b6417903101d48107641d0315850f001c005100358005c3c40340c000e0106030054814412a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 187306465 1250 187305215 187305247
    0x20d022502010807031d120901110f0c0111010b0409200a030c0302060a0909050705070303050f070804150b2101061d04020423150108090d0504090213080d0305010306050f0606 77
    0x31088030400f40e40242c9460405c1b030715010703400380820424400441c3c044919a00032202d43c07013901c13800002c2c069480c0c030401001d1326031211001090610035662100780641c40c09510009848101400400a80013907081049500094044c56a00740641000344480e43c101140c4600840394050380e90f02c00e2a04660070403071142c01c1024803008100b07089000080c2d20340103002e01e900501958840a54134222030a0080640344014000308444000805008620b0781c0958402e5200c0d802503144411601350b11003240140a4500c0780e00e5010f03404184201e019071080003a070980380070f0380c0c000b040010b82da60008452901061041070445100c100000c0250510360030a1400c11320b200120040c1c05a10139100c1c94a40c000c0e510000c2d05280381424188658001c1c1c612600800740c1e031700030100c3c80c108090003009445030380283c1e043d043d00898000c0075102d8945640001c2e003201000d071088a02100c6c03000300100000d02c01030300d60604180100d600600c03000d04d0356010361005080d2514012507401c0320316507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 187307715 1250 187306465 187306481
    0x180d021c11101a18090d110606120708240105091909080f0706050906010b0f0405010e060d02041e0b0403030f050a090504021602090a0b091315020d02250201080703 72
    0x142070f401d41810071850b581e66450030300e074004854495400d030901004541c5420340314013800040c8200a40a01030700c240000703070181e1105003100c0360400b081c070f4200850308202d0303158480e140920501c2c00c0b0400c0444d0200414000c1505000300c100c00b40c0c0d903842001703005a000c3c1c0f1142290510710000342c01401190b0401c3c06444d0180600f545000746411203828250f010741c0040c0c4809070303140144661480c05000f05401451001c54550070402d03000c0c03039010140f0680c82441d060003250040418140c0310041903920140411100715100ca540d24008120541c9683d504001c54119440204441603c0410b5406585d0980d80e0b4000c2000407040c2235800350700c000e0b201800c3c00031205000640d580c450004058981d20138000d00c0090100f0320500808540180180f0262400c0a10070030f40750700d40303101141d40009510700c250200002801c06000c100c512121105245000080300e505108440d0014855928128440c14003c200207200340d4141400d9080240020407503c0400e210394400d40168007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 187308965 1250 187307715 187307741
    0x90a0b09123114011d0109050415050d0605040b0c040b0a03020f0c010e0c1e0d0618050f0705090901021e0f1b07030c0b0a080f180d021c1110 62
    0xc0481c032003100740d02800107254019803907440107103500d0f00c01d540c0c07111490030100040703161445400c0201d40060010001c50107244d01841c0e40c1c0f06c5100d200c12104424a00030400a401044803034014104400a0310382103401340c0d0303c07001900c0400c25034a003c41c200d804560f003045003a401c04041c00e804401a500c54284100a52000c2c004081216030078403d004414051000500c80c2410800a0106d5a00c2d4000e04d64100c000300d044400d4151178403070300310a02540c0038400013100e014510702000c080c098203030064203500c10695404d9110b103002480c101920400c990980040e990b100540d4240e102d2114540179031402c0311810400c40d62800040c0201040044000741007207401d5000041c03d48c0399454000055000d40c0c1c00f0003c0c840300132207000141c0000800c240c0340103408400544185005004090f1090034000002c420071402d0030300d403010540840079208010302c002c0d002582d401c44a142c0980d0105102c03031480e0b005004007410740c0c54800c090040c040303412141c540480140510810a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 187310215 1250 187308965 187309027
    0x20d0c020613110d0210020d120917130e010305060405010b0d031d0f060f03010504060504090c030f240509010c1e110f1f0f09020a12020301060905090a0b0912 70
    0xc0061b5601c106007201d0300c1a80c0e0003888050783c4c005005000300080301c04c80c881c281c03030b00c4415400f103851f802000c0341c020340400020740d0344c4501c4800c40c0b041700c9007a0b110280c4c0180c180d0000c020840c02183c0307180603c1c0078000910000440c5410441c1d6081409401400300b4074406001a4200da14040c1d484082d030010094085800994041011a4080c1c692808038920002c0184018030746403241501820095508005103540e0740d031103108030722850102800d006041e071144410407402c45a40202141000581540008040382003800340009a4000c00c0d1542069610304015110f0100160100c00c5188645c0042c0701100341550303842d08056242100340191071134004c554a040140703030070f4001964806402c555000c4140022510100c040e8146107040c206004003503500e4101100c16603402900116019185100007030043c80c603070340400c042c0d030309040030815183c401094142d07020b809901c490440e1b550785c2034001d856800c4602c0145200764244000c0c21215484181203400c421101a54 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 187311465 1250 187310215 187310239
    0x601020105131b081b090907060f08090c040606030b09070309120f02010216050c0a08010e031801030905060702100b06040f0e0702100501030b011d09060402011805060706020d0c02061311 82
    0x9504250b4103001c2140340c1e400460301450a810b151801b181d1002d0b100740a806c2040c182103006140401200d2034408201070280030800f090424454004448001402040015940d400107006440c050301824414200c02d4005912980a80203842031698001801c4540351791448080d6010303d180f008820440d0760030b10807028034000ca1051900500c0c001c0d40101640881340080002846032500082c65a904081c85010500c070b0000a5540088210190086208070800102c000307003c0c49102138100d10408050212050b004540c540080c803909000780003c0601805216492040d413144a290f440000c2c1c1c02c20000041c101c9527900300b402c52055500d01d4006101100569201783c1040c0c03848680c2c030340100103004a4007461401140b06200070942032134044411a112840104064180083c1018009203500303207800560140c0030007480e0585418030703400c001c8002c0d00f0007d014154180ba090905d0449400016054400d4001c0b074130308401c1c00d0956540c0740b001c151400220350002507240348 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 187312715 1250 187311465 187311479
    0x1201020904061e0b0c0312180a030e0102010e0307080f0906040f03080c0d0305040f3207050f0105070203280602040303020309090105090714070804050a0602150601020105131b 77
    0x42d88000f00140c920316400d41e83c0091041d10800c0d5140c2c024452094108a020307018030b0040252041101d80c40000c0d503d13682c03800f141d009038200000e80f255440c082c004150702095085110a00300800030b80c02000034101402400d1b41c1d904c80c404018100302c8080c4a500e00c200b42004c02005040c0b0064422030609680b05254900702489403c00ca4013040c020901c600c580030200b200c2907040403640b03401d0082d800c1a89815042d41d8820344050221203025401006400c8a18082242c0344075130300c0b074443d50000740d24100b078440c03840e409550306c03032020401c807031400358428000d403500c142d0010081c220200310440042c62554080c1e1117079100303017054081e48000c5a0144094002180690013855680c034000d0704000c0c2c45c1e0b0b4142c0103507204e002d80400f481078a60340040342d8480c03440081c20f050f503a00d240341490540c1c1d010b05d910440d4064030b000f0300460303440c2d03010411a8440203100d40c2e030035803511a00010381c2680c41c05c0700c00d081200220075202000c2030000484010b0168104071440180d619505 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 187313965 1250 187312715 187312721
    0x307150e0703030c03020c150f0904110a1d03030304110108041514070e030d05180f030f0313080105060916030209151e03040b040201030c09181407030510051201020904 74
    0x2c0240e000c42c14800441e820725806006450424000325503c1040307406418084400d401103170b202c52a0341402240143c09910380c2d13848180f02c081c2895140e03444900446002f0300c200d914504c0c14003080400310600b9403508001060382d000d242d0260144007916220401100c076004c00810989011040078000381c020701c41407140d565030b0340311031080d010280740c000005001140081c1846019900007100c403030455a0240940e0b06102050008000f5203079032800043c402d03e00382600c1685801118000180580d0020013003611118403060104401e54403c20a403c981c022103610b41c00040c071030006000400906000e01d0014110f04005040c101607a000c22014998001202e8a000c00010700c8000c1c00310404494140030602c454140c80d524140d42c0d549080140a03200030306058441044401040c082c0021402501f503914501c42d01c1141d610820014152401c85501d60400303060104803480c1c482d00816101b00515040308c071016103407000f4000e140600884001d11554244003414190361140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 187315215 1250 187313965 187313969
    0x3290910180b0a0501111c11060c12070f020703030e0409060c11010b0f0a09050a02070b0a05150d080a0f0203090a030309081006050d06020307170c1306050405030307150e07 76
    0x2007000034040103180240711000c2101e80000d41400403103400344100600005081c0c01c10a1802803801084c02198010758081e12003884503d4070740100c004102c200d000c110041e0a100d00e480c0a40ca0803516051819590b0307810354049d25006821136081400400d000e17140e0305550000140000440248a0712010120b452804181001411464950044403424050341c108414100c541d4061020391500090030080d041c4502d2040c103845000180242c4201d074140c0c0d140682125a07002145070201c058001010102da1300f0034074800c40c1d401c400443c10044a841d41e50780d8001e0f0603528000c5030a100313039901c00700b0826020440c442040800036903180c085075140118400c0e21341255070742c01d01203030b58100280182030960003803510600b04060f83e00c40d014a02401d4002d0720040c0e41c0d882d8400122141802c40c801403819008031800c1c00212041200100304032812039540c0d2680c00d4682d58125858800c61140503850351051009101240e01042e452042c04020440082d100200310001400d1000c59 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 187316465 1250 187315215 187315259
    0x905070c06090506040c05061305040506150c0a0b0108010b0a060305060a031209030311010b010903032105151305010503370f03020f060907030305070201020102210703290910 77
    0x1130010b010030050010303502409864201c90050074104003242d8804000041c4c40350754892030310340010407110340f1103091031401c0005244c81e01d40d507041040c041c15668905560102d81c0f4424000000032191010303c20712030b402c4402405480040d280440071006030601a00d103c2c0c0c4804200000000140e0015424014021988440307641a01c0c40c20702410110013081410660f904104030300d40c0c0d50383c5c0041944117980e0325050030601b50b4148600c0d180c0342000401840c4506240c41300b4802c0068414002e610b81c0001200c0c01802040b00c101c841054440a1181d550140d0200410301c25041220342c00401003070003641502e081030a0300c1c404100050505c0f0003580c056844205050a041d410301400381d100709a800240801e00348481701c150b5841c668031001e020460b0114400085a10031f4040381c1c0002d40d80307040c500b80032468550341110440240c034804d0110345842e107092a01b510100741800c000ca40141b80c00441c0e0406d0040c0403001200920400c0e000f1349540000c42c480fa4100100c2e0b50003e20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 187317715 1250 187316465 187316473
    0x2a0807050112060e01030209070c0b010623090d1707080d0506040b0a0605041215020703020d030c0c0807110f130c0f0905031b03030d060b0309010c030b03070905070c060905 76
    0x40c1000252800502c0780b88100018104401482205a20b16906044075815140022036554194040380c030185003400042010305100000240d05074450442410502d4400c1d180300701580302c41078a00d007845513000840e0450045100d00c070118081d00e07410380c1d648009201041c0340040e140d0795100c1c160700148031244059621402d0019a007024072a41040100c20380e60b900300d19041c48005004d5006611540e00c09480c03080200c010801d0740005980c49103040f042c08c0d500c45441d881d020b901c91600c5940000005d28041d80000030034070640c22a624560000707046403400c9100d86800f000b00142d4001c841c0c000900d283e5414180d1101c0c0c1e20f11908140d81c00000814040b141070090012030708884c0c01080040100013800590b4010881040204000a40b540ca030005100401e0450040e40c1c800e0311810701c5e02c2c03400100c8100308001140304017111300c02003100009014040c4d084814100c3e407150158031511052140d103802d43c0c0041d40003005070410319078a00d403513aa404265401d8040840700d90b04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 187318965 1250 187317715 187317719
    0xa060302030109050906190b010c240c0813021e0d0b0412050703080f040c0b0a0c1403040b040501320406080a05060303090420040b270307032a0807 65
    0x3c02c9126040e00314242c003018100c18242002403489020012445064980c2c7d540540719140c0e01505407170903500e40c0800241144203074000e41c50307920407500c1c0064034001e06102594041d1441550310354418141d1100225003500300342c00b80064020101034001d14020380500340320031641d50140c01c4800c6445090440761350300d85454051980001c40d603000302030250902107480043e0f0851348080e401481c0c8200280203940b1814a000c045000380e0211104a4000441d5612241d01129844407540074410f20450421060001da03078070301c218402e11040710018041401150710034201c0ca100550124484842c1c030402540000b000004030b43d00720030311100090100111a044400340d644032030150000c100d9850002c0200391644600d038942c0c0d114585e6840c88917482107400a604c114003801d401d40544664460440000d0350344110a4140409450851b0903460442d40c0310096015a010300a000e8251455690a12003030205210061a64403000d040440542c122102002401d03850300610400b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 187320215 1250 187318965 187318979
    0x12030c2d060103030309110904080a0221070210180902090906031f0c0c080711150f1206010504180501140a0b1803010212130203060709081506030c0a0603020301 71
    0x906445008503054110920814600c0c000c503078541140d40500b404200d1411600d000002101150369050380030704410140000d00c0081c43c06000d00e003100b602180c0c40200c1802010f103c4203000c0103207640804042000c04018205154209000c081900f404c1d660303051302e00c04090003078649030803903449154045540061864040c48698100c8130540181c10030414031684030540004c101c500301a00c98a07960f00c0001c0c0d0388141780c035031a05508001d80a454442a240100380d41c50002c00d1f903032003040c450704840104020442180c9a141900031345920300401020445044000205441e05100c1d0078400001c520608481c22001c51a544070002469810484441c03d0303d40b2400d031a5015440c1103030284144101b0904035610b20706140c01200f242200000005e005e0f1145a001c200003084810900160840318007100c00060701c03c0b03064070916a9185401c54020f080c40c403442800340d020345144107207032140d0888280c20020150545900c0459400460701b070308010380c4031100003540080108465 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 187321465 1250 187320215 187320253
    0x2130f060c021503161805041103060909010621021c03170703050601050706020f0f0c07080106060315050d0c0323070b07080a0f0e0d061e061a070212030c 68
    0x42d0240c41c0f0030780c254108114041d43ea9518048800140b010b20180469205900440e40000342030041c401d0104180e00710340070805800964240703000304c1d00000880c00000c01802074105481c8a40d5405000d076080d404c4410416000c004180c0c0c120078008001d0380e14103800c41000010600030380320002044505e4050f100c260000130504010145450140031a907079002d000c071244180c000b640941c40741034030340040c2c030280704015290940c07036000101c411b9400f002055203405c5a4a1800800081d96140419019155220303201c5c0204040d0702c0b424085840c0c514071b0640c4a9028101c49000c4c540c40e5a00c43c440e202e070f540301a007000d0303038076a5410900c08402c008440c060003081e6074550030b01c0003503603c11100c0d00490f078021003030010001201d80c02c03500c14a800c2140d460000c02c003071441e007118201030300201210700c503a485d80c000180000c07442c002280038500445207280940714501c41c00026020345a00300c0303a01240d2100c4002500e080381c2d0000c1001d401109112400740c002d02458010030900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 187322715 1250 187321465 187321489
    0x12031b0301090504050d180501201606110705060906030901090218060406080f03040608060d0510020304030305060612010501140d05040c05091810021b0a0606050108180a0602130f060c02 82
    0x80080440b013817012955880300187c05c0714001c2c05c0042034040e40c0500320300c4184901d00c00503000e102e0b1807072b40145242c14001c6041101d00300e4450704c08840c05800c0343c80d1208001c1c05225045441045040d40c1800c02500441d40148004000140280b40d58009102d6031103084205011040610034080c00349494800d400092040c2002095100000c0e00d1454403401103105003024000c036400050000d4590b100d810340c10315402000d45a10b941291780c0c060094005640a50020349480300107241c5041c0030044800d011809109005980c4ca0140111200381080c84e11441412003406080c2d44181c981c01014015803080340b4038444541040248034105070000e000c4484541d0f55421041100c2d000726103800c812455040260355038180d403207010103401c45018403200901c45d103854502803000a1b80308009441d0240c0e10341034503845400d401782c11051482c11071030075a0490a1302c01c000558580c0185443e00c10015004505a0b80710042213005d081a40200d001c11122140c100c00c42c0380031000e2801d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 187323965 1250 187322715 187322717
    0xc130b09040c030209150d02040e15010902210106050702040504060b130e190803150307030804090f0516020d1803080a0f0e06120402060a090801050a0b0a0e01030512031b0301090504050d 82
    0xc0d819182c0c000501c0c40c7e080c064000e030285a13a00d0701c15000311014010b07840000c4d24148031488559507444203070b009501102400b880c00500d801c104401c1c002039280241282ca01b65030382414011107400f0400208006081200c010340c0d2025001c000d43c075404c0441c6156403800c0000200021003003031107404c000c11720724040e07040c40440345020b0002e17102c00b064a0b08580c0441215100185040101e031900c0c2c1140c10103403c81a002c038000498040c035403c110030700050103805006544501032150b0704e4440030b60028015070450020940002c1c89107100c034829450808201d11000c2d900c5c2c0710b00c0c48603840340c00c0400005d40317407402d02c90001d500000030600500050b00c0d1240b40140e007a040040e00c030f0000d0002445000002042420b241c0306030100c9016000c0c03080204800d0030800070380801030032013002c2c0c0e034000c1e1100f510011b482200d040003035040fa074000001c4d020203001003108071003552004040340139136161007405004502c0d0101c0510301074814070380002041c1c1410f0800501c0c02080402d444 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 187325215 1250 187323965 187323991
    0x509010204180b01091a0c0613050d0809120a030906020406050306150408070e060f0301050f07020f070b03131e0807060b042a03090614040201080c0307020c130b09040c030209 77
    0x34240f80d17401644007080f21824100900d00403c0c0a010142900c2581e00c103505070f100341e0003030103030f18040d680100201d04d01c164201d5410004510050354406021034024820390845040c80403969001c20003031180c1c045a280c00030740c1003c6991444101e070029048180043c2000c010407045040100c404050114103070002360400e031034084a16030f5000c0d01c2c0504020100e00501080d003035181c0b00f107103d40070744005000340181d2a1511780e041d4403400442c0d025006100d488c01008a900c0041414416541030f10107007403840e40c40301000601d9001003207003180c010100425481c3c1e213042040360051194031900b0403541d07400440c180902510040404184161f15002030034201449201103101050811202c00b09800314451055004285c0d203032018060908068990070141c000581c0749205e180300341c03a070302050344440b14011514007044400c131000d60321042074a05c4901d45801ca0702c0c00c3c80300c0000d020034408000c0c4082501c0e90b00030f49040f00c840b000140141704601e4000c503080c2c1e0202c2015100c0d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 187326465 1250 187325215 187325231
    0xf180318121b0b2503090b071101020c010e0d02120a0210171e0402090601110d0503060405070305071d030a0c090b0f010509010c0b0c0412081201090603020a03121101050901020418 79
    0x1031001d10f22000701c1324a41c6002440c401040500854840e0700401c01c032041291103101ca82041c4100c00504808940140140c03207a82c512980103921200c9140805050407071094083d038248400e483c5018408103292041615843c0140d440400c01c4007408106d654400c21821740c030051100d022400750040d02c1032001e07419055824003514800d00c2e88650100c0d82400030383c540c0001a118046030740e00032100c9000e14001c82017245e0f00700006501820041d00c080000d951619012011101d00703503030000005a817810a940c001c50f0320001440c1500340103050325081c0b0003950760424010b13201ea01603200d560701e6080205140c98200c1443d01119030a0130500d107406110f10000f4481c8a20040040010721400e01007036490740720b40c0035600034006041002420901d0390916404980144842e904801140f200109491030f040c01020200d941c0078204410142c21640c4030065000c1f0240600101f200010100b2002d030b00074010300d8011107907280010390740d0f8246009003150340e00c1c0c03002244505d4101148 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 187327715 1250 187326465 187326487
    0x20a020d0807051908100b04090606081b09010c0302030d0c090303021005041e170f0301030c08240a0e071403070603020c0709021605030301180f180318121b0b 70
    0x5103241c81844c1442060b0b40c0d40c0c6c1c02449184107a084052074040104010401d11240d45c408015034225480341182c60f03940e041d58030b040107600049003e05044c24840114294016100070058510a0041d00d0070b0603580d210105c1125001c01d08540040d180600410502d601171003480ca90942c10304082c4007902d819211030310403d14506a040108490442000a1000c0b00f45c0407000c40520481a47da164100302490555030420700098440c2d07165002c000a0078540000d40e2441c40c0128281609045090580c4030100030005083c650226110744c802d6000700000c2c030a840160110700c8011101c444a4028145841241d8100784c05151040007185801540041e80c402101c0d518100540da483c003150000d0240501198020300034440130002050742d045d02c4028104070403c0701300c2084400b144529850903143c010b45011011004080c220000c82e04c01c4041008030340b540204426025070b201c03050780c1c00101c282001c3d107402c2e80c040000b50b041100100544001c1c00b207498464107001c01144 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 187328965 1250 187327715 187327747
    0x61107060f0c0c030501020901020706020a050606150706020d1e0905060612010e060a1b0e06090910050a0b0919030206030f1513020a02010b010203040f090905010e01020a020d080705 80
    0xc0900303001041240c1040c0c9841074201c08807065100561600c05079607407800d1070103504115000c83c0035000f40480890000e00c000741101001e5006002802c880d10390303c00740720404039003c1640c00c11074400c00c60030001c1070b80d500042c00c88590f0403c0009000c04550001e40c81c000302c8032070903030400d0708042050021032400121280c120380100c800c1d400c0340000b801d02c82c0c010700540500b00f046001d580d08010039016103604c036400381010031105102540c050941200d400c0c100c00290396220708240301c92a0705003040c00c282c80e84056840d4038030072038a0301e40e000541c1d0540e142d40b0100e104240094007010a0915542a1085a0040308404100382c11035000845038000200310303612040078940040c40320580074503003141306900600340210201d14040e14002a520003d01c400143d820003803040182c0d4800421142100c90512050401c81c0c2015600005407130200c40c251a25901d5415600c0d01500070f20003021100500e8005007465946601c01824014006090400740542842a0011080000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 187330215 1250 187328965 187328969
    0x1090b0f0a120b030118030e0a0b04060503040201120e0a06110403020906060703030b0d12110d090603021806040b03180303010e0c030601020f1204140d050a0809031014040b01061107 80
    0x4107240034071000302c002c01001040820003150303056003000c102903019400d40520158040c0603a17a50804040c648040c005403071514413840100d26002c01040006600c07443c05503800034414500708003019040d074421030a958241301c0425558100c0317410602000709621501200d00c15540030a4103103465900026100d090040071180644800201402010b20982c440e800781c0f00000c4c192481441141010111907080460100100e50701502c040405140044d4032071000850b903a65184c2603042081c220044d412034140d82c840601d802181c4000ca41d180e50181c0050844072001c55128900417108140e115040d080c40941d036001040144580310304400b80c1035000300c00c1c2050994a4580b800102d1914a804c0501191401a80041010210608020412507541103040786c101388081c01041280032001a009095600104071000040d0710800a42581d14008007954401864041c0c00da06a500e070205104403080041e04010800115019060162596190800c6001c500641c1169a01124 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 187331465 1250 187330215 187330217
    0x50c0c01020c09010e040309091103040605090105042013112115010e060c15090d020c01170a0b0306070e04051005090406050901021606020c060c1c05130c0e040201090b0f0a 76
    0x520000c6d003814050501c9100504100c0c04c03c2050700981c025640f5070350000d9500b1980181440041040309105002c1c56004641103030710161041c2948a801d015132200000703240e00180c0280307400c0080701f0980300d0741d032001e9004051170790740d050503610754184402c4020291209a216100303000e1389921040aa1070900c07400e08080c0e09a13516400000e103940152900503c1910840c4540300c1415003200c1c00702d001d003030b01d034007181c1152080c200142e8980c80013001060002d0325030400b1102c0401e00402d055003003401c803030001561031030400120f03003803141c00c0700c1ea2008902080302e45000340c1406d1046c5540540452454010b0902380400940c50400c0508080e0105480b500400c1c0160000e6040312020740b110460000045014079003600a90000c2884160f20f00551002408070503450381101d50010a103038000d20180300200a0380011b0401915412102600c0e58181c4001118003840d00e000d07080003004082e4500d010300c0014100c084a40054a02c640c0900010b0020341100d41943c6c005105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 187332715 1250 187331465 187331489
    0x50d08070504120204090602030406090308010807050f13061505070c060305011404021b03160506010f0605030c0315030d030e010c09140d050109082101080307020901091107050d050c0c01020c0901 86
    0xc0f078000039014108081c80501124030020512041040c40d0f80441d0041d40310f40c5550010f6070b0307118001e17501c0d84964030582e504105d14550340740c018505076540312260030000070006012a00c170708502030518140049100443c42c0002c000050101604a4030000c04e028601488190b0400007605040f0070b08417041070041d6000301d4041c1c1507800341c10340c2e850034003e048200ea89541c21410504203101d6580320940d064000d4030008140c48004108070010380e0040d031a014910b44a4510290150780000c141000e2001500501d03ca199018051749505101079078010403504200c175000c40c21a0040b100e08010303ca5544010003007424505400c1d0703400300c000c64400700508240d0400902501a140004002d8400002c08050007420f6480601e0b80d88880340f100100c0c0d070b0300e4547d09075407807280310400ba6000a135a0010440411150090388001e224220810308002c8031380d964901e041c5c0d50003409008150085002860200300308611280105c1c00d1008000441a000115030044010300801d109102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 187333965 1250 187332715 187332749
    0x130203011d0408120702070f060e061813020409020901030b011d09100b1603030e070e0a051e0708060108090703020a0b0d0b0d050106050109061d0906010e030a0f050d08070504 77
    0xf24060310440320581d40000b52924040d00025250400760190b0309107980f0311540070900c04d2140c00c075000e000340050101854145803c09030f18644425100e00c6601c100c2c5400410800c0c40341e40040e00c0103011402c4090b8031001250005826100d4042c1c50358104a442c200780000c08801020149011100342d40c011596221000c2d00c0010755119040810884800912480c0d09160102c0c11442e0b42d00036581003140c8141c048129890713881c0751180c080b020412802003145114280d000d0398001d900c05100310b130704020002d039009246034100c0e1160080740c0d0030760030000d965821280c0e20f907120000501900c1e46604690000700090300c2402070320521500460036001d80a5141c3c8810201c1c07400030012400848286003881c003828441c01810b0000c0d0481400240d014040c0c0110304004c040d140d4031050b124250001d110040d4001440d603410062134041b10102c40c0c45c00c1c4101240ea6002d440994044111401c110349130061554060042100610400240b1980501610140d43c40c403851424040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 187335215 1250 187333965 187333973
    0x40f0908180f0a0e190e07150201060504061d060a0b0a03020c1510180b06071203090804080a050f0c010801060c0f05030a080604390c050a11130203011d04 68
    0x441221001d41c0125a050f004100000300901d014400c08407070310780c4009440c0301c50380c1201756400016a041e07113601c05076052268000031000c0584142da0340c030000500aa95900007001d58010358001d0b1b156100c00c2c0c40d10388601442c0180d9503401502510001c2203d450032403a103d1510608802804256000c07603895030745001481045141c242a641e81042401d001854804d8105288100350941e04030080800c40d4030a1401085404030300288468208005600e82c50300c070074582d0303502c1c40070195558402e0000500001c09030010708501401040d00b1242444c08926042e00b04803184499400450540c00070f070ba1010816064900302d18120852003928503180010b143c40c44e00061007408041240382d00755900c060707080d00ca15012501400201081c0d88195010200114180c1c1e038803040844d22040b40c00f0070030b12140b08030f981d451300400e8200151691810040d2500d0100d03952002401c048540345002074500c1e504500300c5804502e0742d4900142a4815403161500d01d00c501209030008042c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 187336465 1250 187335215 187335229
    0x8010b18031e0f060c1b011e020c0f032d07170702010f0e010207060e0f030307060605151207030911031e07060201060b030606030604091e02040f090818 67
    0x1800c0d0107002c5a4a4841c08030751207030380804808010805200361200c41604820000b207150007002c11202080c90194101c14409000c04915842c0060b176403618200105c04080880c1d00c0d0b03e00000c01401604c40c0c0308003c00301d051a030a03e901c40007661051212140034824184551001e00c24460304012443c500d074008070250280410103060071f40000354040114106c00010600b0038400d9035080c0580c010680c040d1050b26100070521f006074402c100520581740074100c801d283d0b030380c014144540746030300c480041e240d90702055080711225158201007226040249003204850020990035081c40b82100b0781080300400200f01404041e1171341c4d050414003494504001c10840d01405071400c07001002501c03040b00540001000ca9031082030300014940380306104038016607000589042c035589401c2c00b002a03a40000d007455a0041d903c49441c00080c0314011104012010300480e003400c05014010401198621014901c055081015a00000b00f1541c01c45461000076030303010b03d40c5a5150085100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 187337715 1250 187336465 187336507
    0x20415050a1514181824040b0307030606080601060201090305070308040809040203010e0709050418020f12010c110d02030a121a060c25031e03050c0712050d0f08010b 73
    0x40c1d40010380b41404da4601c40c0a92010380054071403001c0422520b603007000c005011101290304c1500d01d014155505c6140c1d1000c2d2404000810104440a45000003403c052480d40111640341d91080e0404c842a400d11450b40180002c4c0000c100b241c026844c064024402c580700201007151000000d030070401d40c442540c00c0d0f0b07400a00115100c1d0303101d00b560760b404030303040c0c0300078000c80d90344540010342d07150078021244c1808084d1410072182c107072582886100c2c2610042c059111180c000300964142c800d204030b26260f0a0365443c280102106058681483d1a03602c5500440d0010000c003c0d07000d8004202010b003032801c0200285400c100f40b96010300d0005803c0603503200c2c5000a1050b0b0904000032026000d44207001d840800c007204040009003e001c5110041a9880700000600200001d0300116161402814250325010480c0780e05410003109401c12a0249101000079007401010440407080c9103490510300880d001c0554090721000051241415510300007442040207801d40e118000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 187338965 1250 187337715 187337747
    0x7031401030809041b050409021c0c0e100c03020607050d020d06060f090b07051504020d05072c07140904060b0c010603060b06070308062b0f020415050a15 68
    0x411961240b4140707445034440740d4428480da040190420300c1303003000515460720b25031540300c1da858a840c0c600307044d004c0d4010b10604000c801e00380300c01c940100d05038040c00709524050754404132880300c904100000719285110350700c10010f02025100010380c0000d03840b60010850300344a5142c6184c111468007034441e407504891b2a0b820204001381c003c2c2c0201c12980d40c46420b899403d5001d4590048001038080c0f4840036215070301800051100b1580384c17100747c0e00170340003600d902d2600040d621024508600360f803200200740c0c42e0992440c514070180c4041044042240d034001d0303035030500c03040091044d12000104102c00000181502c21613582c1c0c0c0c8558001c0041c1c540032074a8490b4401c407940200f0b40380c482a00d489003014590400e61406104a6206651649038100140c80300c10600c4241d4208010140d1103480b01111007000c0013401d541d001c80d15114482001d02403040e8818001600d2071503040300309503466102c042c41296210000350040c2e90440c1c0c030070640000003500031580001c074540e01325 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 187340215 1250 187338965 187339001
    0x1052d160309290912071a090a0c14031b0f040b061c050f0604090503040308031e010e0412030b0a0302010806041b120b1e120106030215221a030703 65
    0x41c0f0020050468140304071045010b130349001152100031001442118001082a00c020000b107c0c042c16484030117030030a0700d02081b03d0303011082d9550f4501c100d0303141d081710100e4003811f01c10000500c0c0400804010842103840d81640c99894004030305074070b501c4803886200d00c0d220b030009242500c6040c21341c1c03e21000441910020513440344407600403d4151a114017203141318002490504080c0038181d4460b900000452a2500e16150111586c01c080d00d060300880d00c4000e140c42c0b50038140f0096010701107041c269a06401c0600c1c0c400c201e40b00c10903c07582418207001c08200a507556041d414200c98080c201490300350348000029004090b4680c805080d2000414100f140c154051a2228240351011042121404150401140c144007003074625010000300d90560842c10241c0f21000c01030704801c0042290303501d03a80050f1038500f142c004021200750100304035544500c1c12070000c030b5610b0303140385280450307090050401c0c0e1281e40c418000e201610000109038164843c0d0304c086214900345c2040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 187341465 1250 187340215 187340273
    0x90a21020910050a08060903030408030c04050d060b010e040b0603240d060c08010608040b06010f0e04050a0f140c040e060102070801050c090109080c0109061103070501052d160309 79
    0x800404098011a130180d864070201041404000803814000d10f1004015811903456544020f2280e00051010850a00600c800501c0d926248807c4261a12035540030503040d141c02c1c001403007410720611691240d41013104040494a0b0001165000850038415000c68030380c8425107205c60360220082d07500401c5d00304103d800d00c4290b91001e50b16244c51ba95014250341e0b0b030300c0129017228054401a106c0030a4001007085503010b10a50000a42c03030741810b400e0f125102000404541085417201501600c507041032105848520640b181200007840786403641c200740790503003181e0249000708114081c01c1c06c0814a0380c0e00030450403005150350320080c0558a000344405003d40c210400b090701140c070421010442078008035070342d903000d041030b520b00030302c24a003040807903d0010781d0014010038082000081c0108e035082c012144a00f01c00510720080520800039410020b0580000d0251106a8000e00c411520107814916010030703e4513011030004041c0c01d00d8001d505800307215890419180d044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 187342715 1250 187341465 187341481
    0x2070b01080609010c05070308011e030203060901050702060601051c021e070302030901020d0503070e091015021c0509090c0d060905041b050f0604090e07080d051905090a210209 78
    0x8183c860b0000100a11100d648290190350a0181d00c0d00140460f103050010704c20048000d80d034411040480c0001030082e030356a00800e080c8441510081c0590b51100c04202155030100300f4103070820310030729203030b8641954130403112050108103e040450036000104003843c20078048103503005000126031250390301d14524001c1d544e07512682c030b405c0c00740c05409030313048005010f00e059903c01e007943d485500c8210742100c06c00200040081030380d200c210100340045201030030200151010712441d0024104d913250b00c102d00000d400303d80304c1c00307080220400521803240c03141c2101980000100d030405072100d1814121178040d1526030440c039061488c1c2020003003407055204d0070050301a2640310180081e07846409218012500c3c030a6141c21203000c2000b00130030900c690180103000300040503160303441d845450250030300b40c558000c5400510040b0f051b001c0524001503402c803200385030030040d19040d290004188111245c0c071401c00007901004240e514a5140c40509010341d500134010301c100e240c8401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 187343965 1250 187342715 187342723
    0x2040807030b06040204050a06081305030d0903080c03361b1201060f0b0c07090c0503010e09010c020a030e13060321140304020d0201020a15020706110a0903080d02070b0108 76
    0x120030b0799000c0201020070700701d04241c82105d050712405010161202c0c1041c07000d80345158040d002c411071040343c0c0f440d080400d0041c805440e00190f01400405d6440d501d0500408004010b0200c83c2a0401042401700d10041e50329039258000680030020040b03245c0300f0701c000100e542c80400749042c2c0201825840700b0760b801e02401000e55802c84800c0e5500c040c404100c1d00302c480c5405029140b41d01400b00b80980c000500280124100d1a000c8800c200c0e00c8607600341c1910340180194001c0790000c00148605503940600d40d0b0b1044800008001200d0f0b4407200030b5403058080000b400f0310610900050483c0c44500c0002c0c4009401c250500815a0340c1c0341c0001d01c2540703184810308441c003800c941200c040c451050005802d002184160031a1a650204801c00740c1c0c100080303041d8481c52010600044e8014003450071010f05035801078494031a400c00ca415030700140c0110f100906d082055842d0990011240700c00c1d40e42000700662561b07000c40e03005000748104e000c05040711100100000c0c0c03a140000e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 187345215 1250 187343965 187343969
    0xa060b030304030c090c120213060e1302120f070216030f0c0806100807080d0801091a120c010801090c0813060e0a0609050f03070201090b030a06050d08130503060108100b120102040807 81
    0x303514003403070014144281c8103e000c1e027110228408036079001040454414210803000c5000108111507010100d80b1203000c07680a0800c00d85e2804105041024805000303d0665104c0040d00143c40114504d400305a0080c66600000f800c0700d0f1902c1e180c2c411700182c20b031901c0180c80048212401c0b410034001103450281c0c203101e01c44c864440c2c20004034410f070700890203210030080c90301c1e100500d900b4805600d000c0c110500e01d041e11014010343c01b010075520f400412400c0304104c406041c0c5901e1510004002485c140c101242c1507003029140420750f035003c5032159002e0884003072050395a00b2440e103034010300501c0350500c80358031505090b00305100d003070f03031011000318442c03070071186503622400740c5680f00e005000c8040c2c040b8a003903d0821000f0460401543c2c0b0080d07071100050801d4550001416003441c909055806801c082000c040000d02c03821164080c0400b2002824298581300701e250b84e507002100b0a100003038940413807c020352180780704051038000000c02075450381c1d11010000d503580c400b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 187346465 1250 187345215 187345217
    0x3020d0f090506060619030902060904020708221a03070c14031c0605090429010b190306051f02010e0f0303070219200f0d0c06090b0c0a060b030304030c090c 69
    0x43c601250341441c0c07500841c1c001482100c81101d5401a411094004142100b17040c0c0c0c004504100e80c0d0f040e5501c501c01854114802c45c245600d03192070303208800110200c2c000340b1050034060101403155200101c0780510883d6403403100c1c0d5070f81e40c88445c12034401d507809d803000f06640e4194180210803030012014040380c0509528801ca8848100c3c0081d0540b04248201794108581d0300c0454042201d03101c08080c0f030414500c03068421028010240e50080007640b244c00a00ca002c5074a445605500b03034a03440e51a82c516081c041d41d030400001404000da1070118030145510f100305140c060703000b90080c4040745410001d03201001804180300740c6a03441110440014020510701c50565074690900c800f0543d002584904260240120b0351201130401d4502d540c0901000d006440c2a03480a500212003807240c1c02c0a851185001c0c00035004c966190003c3c46400001e10030113241d1100040c18103c41604008080340341004c00b00464250701c29038001602070b400c601d0000c80d0b20341c000e800c07408090f0f0305 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 187347715 1250 187346465 187346473
    0x11070e0115050909070f14032706280905031204050606030f0312250e0405070302070807170712021614031509030d090b150a0812030703020d0f0905 65
    0x1c801c4121694821070120641c0074240ca8041002c151096400504140c0b19050002c40c031a41c400304980240c1044840346005050500948004160180b444201c2c0344a034000f480141010b0307150b000a0b41e00321061103140848910345c02150405900b0200310650060301b075a55510400c524100052821181500c4174450798000c20101e08000800d9103454070b8040203903085c040242d40e007a20f0840050400e80c0343c0c011900c7c58400e41220010420790303029031500c4200c0400048018802035420040209091600c1849054007264592003114011540613400840403480845203038010702890394042e10006002c4000c10300250001200c1c410002c20840f01c4454560380c04003003401441c40918141c06811111400c21075140806d0845d422049000603a401c10084001140403034035001c000b0750b842602c550901960980c2d01c01c0382c2c0c4049100b0741d8007013803507820b040b00a9900c0c0110503100301c01d041c000000400c43c074403039416074004c08044032041c08405038603035018000d0070702d500059419010b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 187348965 1250 187347715 187347749
    0xb060403110f030a0503040306020703050403020a0e0a05010e130201030b0420071b0312110a0b0a020d060f05060a0807020a0b010e090c010c12140f0a0302040e010b04030c031211070e01 81
    0x2500080c3d044c0c0300d59001e0021850309066984202c0650460641241480030501000c40160354207581c20000e1700c108030000402d85000c01211041e5003040c2d102d030440013400c209014030309482610003c00d0300e40a080110703050741c80f20040360080090094001d245030410088027801d504072801841064061966400081400c10001000181d50b00c030007002116001c03120050b04c1d00642020804260740703429128101050313156442d0039002142c400c80308560005204a02c02600c4c403c13a03015080682017044001c4c10603004c10070520544802c00c003030003c00b0002030141c1d4402c014910782c1550000300400c043d6510a01815511800d8841401c40e000b0113803034031403551151400b05111038000704003501c1c0700070ba010141c400e61032040c030181c1600340410060283c200261f008085004040c0d6005990350310303100c91800c500340e040c6c00c42040708002708800c001183c0c41c41044010f44e90000007131810340384025002c2e10090504c41802107940220400003401101c0e0182e1141201d00401c55040038038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 187350215 1250 187348965 187348969
    0x510051f020a050316142415040c0816110309150f04030302030a0f0201020702180603010b120c150c060103060507030623040f1103010e070203091f180b1b010b060403110f 75
    0x10304d40502d070302000ea10050994240d1a1f41011954000312114418141846071134046005d80b488000100040342c0c6071000c0c00103400004000034258009071030070001812441114917200d00c120509035200c0e01940d01d03060806080325088540812005089075500c0e592840d02a48a40000d00b00d40c02007800c00401d550101e0060080b1445036600802e07070f0414001e000280c004203038000d02200d800d59a1404c01502580742d01000341086010f4900500c5c409a4200401c42041c0c46a0610004404280000c190801d0005862419264820700104060780c9000048000b40f65641c4555403100300444481c652108182d282501503000381e80c2404107002d490501416030307120040d005440c1d40208010442c01c0c40308804150080341c40d00c1030b24500740d541c50000b00459500044207591203503e1020101d41908240d042e0712601009450b2860f00d0701e004103211903030003000ba883c0440c0c6400c3d04240b800c28400c1d4011030b0324800050800303403225103900340010100001c03c00c1601529001c002550a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 187351465 1250 187350215 187350223
    0xe100e010311090f0d050115060e030616200a08040b030403020f0316020d020613080304090f09111012061403060c07020a050118091b02010510051f020a05031614 71
    0x49a002e0200104608813405028104500450680c0c2030b55a07a64883d0f0280038103208000140380740d42d5800c4000a1a100301410b14030f016110348102c0c044410b101000300c1e00201803240c4404e0008524241d02c40c0741003000c0c1800348000e4010050000028081004042000958000d5002e40c2c01c50341d0040480d445141e0341e1280903103001300c1a4942c68401e0052414602400d003062019024a0034031608103040a24640c180c1c01052150300081000e00580721907226010792010307884070500240710700f40c5032820242101080716004121142c914040f00f8010110134454048010080003081da540c0060f03000c50100800c2640300340105004554941810b005a4403a150010988203d040ca01801914503109070074081003841e00080c80040da0301d28030320900c40c2c1504454071100154140700b200a086800091250b400d505034145d06201648901005440d15020a04048142c0c4140316080c2c0ca0040c01c0d680003000e6101c0014210301074540d89140c2000e2903c44e0501c050658145503140c0d4803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 187352715 1250 187351465 187351477
    0x61701231b0f030112030f050a0801090e1f0c02012003180712060b01080606031006050c030d05100501230a030b040915050411040e0303040b04030e100e010311 70
    0x10000030080030689801041c210640100c941030300040c42c1842e60308092155030000d03440204d81984c1c0e0040d5509054214608031110046854000c1c942200400c01600c900c4041c01102c608950b01d54020040c410200041d03045042146409002c131003040e40514090026a01158015403c0204408040031025000c02c0038040d03810301c140c25559000c01c82c01131600401003040c01849a4040025003103400d243c0c0f0200c450145c074021841c1184072002504005014140501941d408c104001260781d2001540080c0c518928146a60703025138544075103035008051440701214a000300b4021a17007007290785481107803030a07250a25441712071000022035540700060020081420000e42402a200368072130070106034018400110f030201a00c5010460410965030495160307520305100c18050084200380100408540c00e200d01c1c0401140c0b640c8a00003e80000d140205810100f0105800b500c240303031160300007401000c20b00c20304960003498800005d8680b40824900104a5100220361041b102 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 187353965 1250 187352715 187352771
    0x3051c21090b1503013903090b09070f050a08031204030306091e0f050403170c07060207030e0118080a030503060d08030c210f060d06060e0703020a0e030c31061701 72
    0x4081b00c1090410680b100c1ca4400442003550301c401400000700400c804038003516030325004225550078800b0604140c1810781182d4820005100100000e80b00042119a05100d2080814980d107903890281c0242110350000c40301d060900956070000307041c14080c074035000e029a0040c01411201602d010455505030340103000640d910720b42d191000554811640c00c410364440d102d1501d4604d445507022038024800c214002561502d001d4542d69020000711141c01c424045c504d111840c1800c041c0da9a0b402001c024184080030000400640d5200c90380e14010b40c0000d5080d0b580e04d072001c0072180c540c1c070a0400064002066580c45c000031010744450740f140596078591140f41e00d448081141d0342e0303040c10b01140d00c21b07140c540124480310101c05c1c85000b40d0541d00c02503101c40704184003910310415100c4e15402540700300040d1010340c7d00c20140002c800d4403515007054079a48286903520a11207200d040c03200e1410031000058035200b0308a0f07000f1803800b12000300000311140020800110107044008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 187355215 1250 187353965 187354031
    0x30905060a122f03070210020708090306180714040608030a03090c1217030a09050106080d0e0d0816140a0c0303090806090604080c030904090b0103051c21090b150301 73
    0x3c043e50b0710a00045805c074000707004031803070740c001d80b030101059a00440080b98030000104c1c580c032060a0400019400075804541e4004155150201582c2c1d00540c0c400c2d002490107041a0320820744413a480305004d0130b49201070b01d41d42d00110358050090010500101e410001d0742d1400501c05140341003403404958040070820b0090320050000340079030000b40485032031729655126940040d500f440743c2c1c802882d060703000d00f00c80f088100001e0422000f240220b400f4648540c0003c002901420403200d40d540342411302c11a042c82c2d810700c00e07104001c42242d4071003480303600d148100b4030800103510360843e8420340d0b81c1041d10303440b1314606031911000d40d001030031507000c0400b080010301c4a1000c0e04061a014007100e041c0315801c3e0009094a00145040d14120304181c01031052107410700524904034230640c40242c21303031103c08004160103581c6042d162882c10221a900305140b140c4c10003030b901c5411614290319400c014152000e50580144194442d41c0307401e010588214031151108800d0303010014007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 187356465 1250 187355215 187355291
    0xa0513021e0a14030c0d0504261612090e0f1b07030f12112a01050105090f090a0b0906070306080105010b09060705030c070312081b0a0507030905060a12 67
    0xc010303680c00140070280b17404404e101440c074462051240c644103600036140102001c0616999004020140d5100c0d90200010425511042c00549022400780c1e427008209948000d080f50444410009400c41800107216205000b1081c883e50000740c068041000e12035100e4280458501c2e403803091660060100c0c40003240724482e94080c2c20445070110705010046480448099245a40d44c070060b000c5485036041c001581e038100615007480d00c440c4612001300010350501d070004484202c0240b81e09800150040000c0c0c2d4180140952510543e02114544d07140c1000c0a013541c031100c2c204c495000092501c0c4c0300041019050051a040365090114030f49030600b21410702010350702050041e80c90340720410180342c2d00c101c1040420020b40c0110301803c3c1100444d5001001c4c05006800c10110b08800038004c0c0907201d40000326071080c80309080050f9141c40314039094503e1700c06a84070a5020301e0201d00a5074568224a280180450041c1d0070001001c4030a00b4158145204201070360300a80c2c1a61307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 187357715 1250 187356465 187356497
    0xf0a170904060f090c03050c070b06060d0e01021602100315121a0405071a0306031902040e07030813170c011b060c1e03020705100b0a0513021e0a 64
    0x42030034440192000c590300380c6601210081c1d81c1180d0000c158640d54409120080341d26100d240c0d080001d00514a19050b03458a8031140d0b68000b41c0028070851000505041007590f55200102c40701e1258000d41d10748010b078000ea013200300d40e51b4003a40100318002d03246458a10900c2a0a101c41481481040f4a1b052001010211000520450710b00c0c050100c80130095818004039031060784908014242c1c28103244941b035401180040c00c0c00329200c10700501c0303042d0360003140000d88006014620079444510f400090090a900c044000084c010a107001c820700c414400200390350f2825000804109076a2520540c44403640f1201c020b094100919501603580300c0c8010800320178108054070a0507034182c40d0700e42142c031000c0300d01000c140140c600000515804134101018102d60a0443c00c2603000d844035500c41c1e01c070f8034500c0080342e51824000803903954a044040a0000a80401103114014010000a5204076181481803403000c0028011042e14822121303031864a0361031300c40303074201020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 187358965 1250 187357715 187357717
    0xe01050c1b0f06071419080a030b010e060d05060405070c050a0f02010504081606090f08060406050a0e01020c16050405060a180b040c1706010f09050904020a090c020706020f0a17 78
    0x11659800b0700030000c41680c990b1124040c2c541c1a000b00c41100080d40d05040300d91621001c60703480880e68215903040c02c00325408405031041c5074414203004c5903400003100120b484000c88144154000008070b400101d0140e1036000c64452882a90100f00b5915018402d580c50b041005000740315034002003003e00080c44500720031100f01d106040c5942042d03110b80206040c0020744440c1ca40840101004012499114030240700820700000050401418905203540311407005101500c4c0a840d940810301d485c0e000e5002021800b2014003c40d00d41c1c030b541c0c1026448509000c4201481c20007000c0104203490680300781801501c000f40f40c4401d003840c00380340030003080d0811080808a0342c1c480e00b404658039940103140d0070445d1551303500b1480d5503d458000041c0c2029102c01e041000345c00004550710340150404083c0e860844900d5295a6507100054820395950410540d680c1803e4034409015000680f1006507180342d02514000c0e950360382101d0351601da034140a4450031140c80702c00d0781499004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 187360215 1250 187358965 187359013
    0x70b0405151e03070f09050402040b040e04050c0307081e0105060105070b090c1804060c0906050901110102070203030d0504200306070c060912120b030105041a101205010b010e01050c 80
    0x32501c0081d42040100b0722089070000c0340d103c0c0c04104642000580c1960020b5000040c00003110304505050130884d0103040e40c003071801050701c062403a1000c9021b002c4104500503030303004010125400c143d100d844040d2141030901c0808208202c801e0115143e02d010b008951103040186e40c2c4908145282c1c944008d00c100240401d8200d000c2e85483d44d02c0350b2521044400080c4a01241c0d84c184c0c1000d00d8914200c07018900c030141002010003050019a81c050101e9a50701000d00c2e0081c0024810b21010b070092040e258000d605110024840c518404540c00081c07050707015046901620100e900000504544806096807540180001900d0f0600403030500102d280079140014856809683c0c1c075070211000301310303100411800f0030703001c001403168043c60309250001c0e4028025400e055480710394040090100000c1c000d546030010710200c0751444003200412556214400c2540c00d814914002e05410411350300240140c149465103500580881d110321441200400240042c8114000400540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 187361465 1250 187360215 187360237
    0x80a050d0e121501140103050702151b13031707050303010b2b05040227132406030c090b01080604050603100905010b0415030309270c0503040302070b040515 69
    0x40145040610410010060b802d40702d1243c040c510350400041d2046100c00030415410541400204103c1036400b20303542d00380d0704040c4401c82542d1940181d41700c130403050311b0300000304203004200080b10000200d40a4200c030b00510040490381040c4042c00054411060090040d900400040181c3d150b9000103010391440c200700c48003001448240701420f001e4640d1160103c7d51580d081c442076151402c419502e84080c00f00a040000b8070800f404e401200013803440107000e821070100c00a00c42d038031a42e003041c0300a0158908005109212000040c0a14001690b441e200c104001c1031005141c4101d8080720016199019280d860b50108409000e00804041d0140186111800303008403500480100a10920007c08c801e140c0c1c00c2403008450b42c00d075980780400c0416400300b0200c2d4000c14006d003030b500c0320b0b0b20428100c5d0141c540040e001142149503400549806441c41c41107074010043c60080d071280c1d09840781c03140c1d036904440507401940221544900488200c8140c03203080c4009100403021 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 187362715 1250 187361465 187361479
    0x181e0203010b030a2a080d11011404030f11010b01090902090f0a08070905090c0904060b030705151e030c09090a0b060d050708131104091b0f060801081902300d0207080a050d0e 77
    0x141c002c503040c40303200a54080b404200440c0c400c003371150300040c40304540344101d0000c0110360b1001e0002002120f1501c01c2340d01c00c0c0d9000030810080e4403107050040c8a1807002c0d00e00c036a915941c8156070703a12200ca10900109034a000701046529101240c80c04460000814020054407252101c00042c440941d5017a0700d4030480c1c42c000b0304c5469922030400036010000c121611a207540c01005020a0440c41c0080080001c00421021700f90180640b101210143e0707a03021136503148424200141010031083c1d9008401180e070701340b01c130b03482d400503407040c00255921905904c40200441d250400b408004185010038001c0c8045810598802e9a8031402603070350300e906c900311044000d4044101e410500000c0804201813280a03081003c2c54014907030b00c0000c0c0302e070001d2801c0c10503990f00c8200300288a8809012500b040183e04c00070350399851880120118519800c4155580c2e41101d081120003500822900081c50440800c0c0d1990f0303150481c01500f2071440e803010131100e003140b884480b81e020403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 187363965 1250 187362715 187362731
    0x325060818010c050c150103020d0f02061608031008010507020d181e0305070509011a030402040908180a061704260d02030901181e0203010b030a2a080d1101 69
    0x40900500e040c2c0c1c1d00e40d80784c1d1951000c040300c055042c01860130040e00c00c0003240700108016100c100324442880e03044180c001c1d483c0b916100165883c8699001c1c4c51074880518805428056030b440114003401003101a10302c0c8030340d5448513500f44c031011210b0401681140f8003500606001d1001d0b080040044050424205c1c0c0381c60344005c03101c0c8000030705400e210b650142802000410080314001c0c1c04219006145503140c85d888612036104101c0e4424810004000300d011912250000c4840a0b0b00504a64640c000140b80318001041c45202500c2007809030b400290842c028071958106842900c81512251340b980c070341c48250340900c80030701103a80d0f17a100f0b0281f400c88240094030031294400350140c1d5a0a0254000d400d603402ca81c00601c450340315000c8200014dc20214408031340c3c000580014211010b80000f03030050121380b10107501805200c00701e20402140d46002034000e085404000c03a01c0142c81c0c1d4804a45216020720020360340007401e052051401141860708114103074002041c051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 187365215 1250 187363965 187364011
    0xa030b070c23210f030103120219061e0e030d020304020a03020a03050703030201200702100909020301300203191b06050c010f0c0e0d080702030303040b010503250608 73
    0x91010140e540c103401c002c2d09041c00c0003210900b0403454035590003c1d41002c2c404c00a041a520041c48002c2980e00710341d5880c001c4a0003406082607600c86041c500f0007520311801c01e903029207814410f8040c0c000940201034a0000c0c94800e03c0c41c87d00b01174005604281405c0c2002c1d0080d40f0140c0103a82c4150789150000040e61005414806180b01e20041d060ba01d02e180740107400d40d104042941184089113032025a030061a00c16a056640c04942c5400c26584131501900d00c01c3c0c0a070010303114507000100110320000040f03c0b00e0803d5240349034010140d50f0001c401e806a00014030000c0d40358020f6124011503e40c15002c200182d802082c05507043d021000340248207204a41c01080801c4002c903619008840030f21078122103d000750b106001c5d819603014010038440b071120082c0c0c420700c040d400100a0000110030703075125a90250403650750313080504280303126410034400c651291003401030b14102c20400b544402c0c21504441e20300b144070f500f09501610900c200814210f464016100762140d41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 187366465 1250 187365215 187365263
    0x307021201020c06070905030307080a05090307140102070905010b1812030a02070906050105090901090509190c08070b3606070b010806010807140d17030f010e060a030b070c 76
    0x44200d010005079a210308260290038804000d001c40306003d2200001c0040303450100441d540c50740d011661543d00c41c100f40781074a050240072451034061045c1140444c15020111040048100903001c031540a42d42e550b50b0010344209028140c0e442c0d0003440141d94120b10141c0d10345075200010000c5004641c0c600c8043c2c9913401c080d4410005911840c01080013080c2441014040c010030310b8003514150000300400d02c0c1d4407040c490b840c1071076620340014000e00010b000c241000401c00b00755148820301410004502c0481d8000c05810780110701d00080c0d1703610740c0d40882d007030262440c40074509200740440e502c0384842c0e1000d5041c1d12065082c00341d0007907941c413401001c52a01c110f20f800d502e5410b01d100c0b01e140940507040700d68035500800003400300454000d95042c011074100e90040c4d115150707241c40901c6140400104100c2c090120600540c0099121282d040e00d049820201d51580d89008120142c1520f2202408002a1030b0116203840d1050790720004450103202c00d00c407c480c0a1182c0d07500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 187367715 1250 187366465 187366489
    0x21c0b01050903030f03010f140603130507080a0609050601050a2115050c0a021b030c120c04020304200105040e060d0614010807092a0f11030a0c050f1501090e030702 73
    0x175040c00000500914143e06070510152510300b14a507000604400460058400600750252805481115004229040294802411080c1c041d20000c000c58900080a800f0300301c001c54640c0074980c008242400d003240d0f01d0701160141040e02c44822200c001c800087c166000050354255045c484401c0c0715455402000d0081002100366551400180d070000c1c10300e00080070064410360749810042e06650005000381c0302d406c0c2203c4110900c01c12405292404100101d0703107800c98000b1003007205000e11058403c05d140d0b100c2000204503a203010044409105074082e8001d10895000420b11a0400b4a950102c46101d481c0000e882c00e40f1100440c141c030002d0b03100703c01642c00600180300c081102d00809000c003103428018a00405103108003448047d0540b4030178100490441c40305042072140900310310850681e416240d941d46035500c014420490301c40152003a04c82c0803c0f1225442c40069140312101410001107216420118050090720303030790881031000d100c24407101c00566a40000111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 187368965 1250 187367715 187367737
    0xd11011b0e031005070801050f06041505040806070801030b0109050c130e0601030c030605150705031b0105040c06210f1d03040501180608040206070204020c06090a06050a021c0b0105090303 83
    0x6400309008040c600550840c01c0f5082905000502c550315800c96a03060645508907581ea1010003490003240c03503030040b54080e402e003803259261f0b01e400c15045801403041d43ca111040d11580d9850001c02d9420400030310000309103000d00d000401682c040c940c071154010708002c5803d49800b11709203213500c4010058200f2407040c5815800d0049075a050710941c01001e50b9400c4c24003d0901d808006031040080a4842016101c0041c84a0402c40103000311491018000f8002c05412144a1880e00130030044034229142c0d000900e001c940c060244212a07010222040d020002002c0541610054207182d1920481151614a0902103594030340740e85280004d040c0041d80c0b10b0385800001800105680e030f1007c104c4800308010700ca62030f4400c402c01d5001b501510f809030b46500920108000748070b040c40082d00d900403401400078480011a43c02d0034a4080d51061001d5100e40c0168412032013041c40310002402140074445c010f000c990003c002e4681e0506110341400e8078140400d0855000d0600350b2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 187370215 1250 187368965 187368977
    0xa030c140f1b010e06090f03120d09060522030309080f04030828020307170415020c03100203102601050106050403120201020304150207020a050a1202031506030d11011b 74
    0xd4410090807200d0310b0748030b6003441d10503440c41551021072118411300e00c4043c0a26141d00340d143c80c0d0340702081303004160721500e0f000a64440c40026a1b07001840701c2e9004449403800c00002c01e0141407841d404000d03000402d5901051000c107994168020461164102d46000003441440b40780081c01d030141c0000e50103101865600d81800c10a42d205403414030403c02c5a4018003456a8400c2e0f0000c16501c840e540100701e101c081c5042c16000c100c40c080e40e4481900702485003d012800d40c0d012030400101c0303c09401b1030781100c095403440c4080e0700044404100c000103403641000741ea001000b9907403c080740b40322032220296181e410a820344009070070203030100d00005410401c008484031561001e45080c402181907007130550701c2c04070100c000c0e03030211100d90b000b296202c195a60015031000230000149803120079a03490907005141480100c05074031074041d4200107080800055101c078401c003801130252840c1c0748202015a410546040340500940d078a107070390180c05411005411030b11507580c80341 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 187371465 1250 187370215 187370233
    0xa0e10030603110d05030301030b0c07081309050a05040506060f2b02010206010911030606070212060103030e0a090e0717030705070e160509130b01030212010e0f07110a030c140f 78
    0x2405160b90340003c0303070300480340c0c0c0c40b01e040401c1c1e01100707036811340c0c3c0d2010501e00345889800100385240030714000039104000c00180513148507a4150b01d1006c03074240076818496070703a070304c1c511301e00301c0d0011903016100d50007400c0080e0445c41d01a4410b01d0750003005080c600c00d684030620945c0c1849101d02c40c8024440143c103028103540c0c0420190b401484060b07818401b03040d2101c4000250300000d050345025000100304c100455640320780890540384900102e50715581c0d6400c00905503903140d03101a000d601184c0300807841c0880b50140307440d500741d120014440c0d01e2400e43c0e40044030f00221010b01c101c1c0010311820000074814450b8100800c110340080400d810030348059400702c00403d000000b445010031240c40e003038031801340001222110180004d00c040624006801074030548410454181040c00080f4908400348000c40c040e261102c010070455807841c100b514002081120840680d0101d040305001038400c0c04074652240c810000841018a00b0205c0342c50081c04c0c1200d41040e8200340c2807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 187372715 1250 187371465 187371473
    0x9030201060b0313060c17100f0906140f010302040302030a05030c060f1e0702031b0718060e0c09031c0e01030c02010c0507170c060702071404050606030c0a0e10030603 74
    0x1010054802c1c405250300d14186180441c6070002494001000c8580700c004081846003d000c4520205079201c022452620b0030011081001c000c83c01602803400181d8004a0701d034196211312003e940c5801003c0d11001e050070100b02021056007180d60401d40c080201000685040c0301c0642000c1c86400219141d1000c00800b50405230000d0880503242c260b401000403140524003a54001c1e01200980c400d140c890f100201d041d4400c00c078080802c1c0f12802030a103040780703001412500312645680701e803007041652480182070710458405c0b80305401c06600400e010084010003440c80761401030444041d4510a8a00c1450a01c010201404127424000e59030701560107028103070190605200800004003030000291583c042c2d010041d041400103800d4048222008085894003064001200c0c003138541032400940c2c910240c0900c0d407034054400c944482387d0038a4056240a224000d05050860343c0b07940480c046034004801c00410842991140040f07611030381c1804a4186031550301044440c15824 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 187373965 1250 187372715 187372721
    0x90503070f060513021c0203010f05090d1e02150702010f0f14060301050108121602041503050d09080304060c031e0905120a081b1510090608060405100b011202040909030201 76
    0x11040350741402118185006954001c20743c448030045020010b1046c9084c004640100200014062060700d02402d0208056000416540314500f030703941e0002080b40c107042c000c0721588284200f80540d0010314440003120358030480a43c4207101d84000910042e00441040c03e40d40e51400d1103003099541c144842580318410300c0342c0d901c103105500070310403545008440d41d9150020a80304407400c4003c01c8c070f498a8410780843c1c6400344d4008109000c08840da01840002e008580306c1180d240c800c41e0344038030000e800b42d100031084a03403800245040510b00f49050700c2102103040100e08100c0c0da12001e490610314110f542c00e4140300c60340c035004414102005d11041501c4202d01482c268808403491001a285a049400011440940c020b006031110000c40c81e000038030750f4107001e40480700100a800500c60248204540c8c92030000d0140c80c0c1c2c0c81c0c031a16140e150565001d403140d0040c5d401041e08862300e410420002034185494804000e000080d80e080703810641020512070380780e4048005150b4240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 187375215 1250 187373965 187373971
    0x12031a040b010c0303020a05041a0405040506010801060c081b100e010f02070c170f0303010602060a0c0309020303070b0c040801020a021e1204090c0e090f07170610050d090503070f0605 81
    0x188040007400611000680311503103100d0020708054000074014802d92090b005e8070002c01103e1002c0798961410080914560018042c0c82c0c044c0385040c2c0050303550342c85062554102c0703c3c04d4a46a044003504d85074004960300c2030702c1e10120110581d0074101d80c030303c080002c5800031442d008000740404103049000d081d141c81c517000a4900c1c0c014080500031030002c0c0079480c02c0740c04000748900308100c010203ca0510261451800e03050001200002d0b00d1500072608901c41c58860004215043e0110400c5e81266405400650142e0040c010800000c2320500000d4201000e42d034000c0c140756450780058207a038091030400700180c01c0403e10989400300e0711920b5884004000c040c0c0f404421078084624580202e2003201a001c0e01c5101511000e40103000a16030307042c0c040c08031102c5140003e2000b040380030a55222000902c041140b803643c6072460043d0b0302a8000a1180c400146600003c031019001082c0c55407010b81c0d02c1410400040007040109040c920803011404004024203086040712001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 187376465 1250 187375215 187375219
    0x1180605060a0f06020709091b03080a140414010e0f03010501060c05160b030402130608100b09090604030e0d1b0801061a03010302012102090d20040b060405011b12031a 74
    0x512042c095645c01140d0b030403c3d01c569a00008031803410303090181c076404001c6a1100805401e1710003006100700740c0300619002c0400c0e203c06d030070319144a200700240d04c114458038001c406072100100f0590b1092049082c10b10004103540700b078800c0000041e007141c5080e807103030707003c10408100c10080040c240240c0c204a203007100e40c1400e141c82c207005c64001d4440184001e110314011081400030f00300720790241010f0001d075801c0751000c0581d1107500d4000d141d00101544a03940c40c500142c40d8003030004021748140e605a885691a00316041403107826040180100e4017180da40441c00303082000d403154800104000000804e8161070f00a10700c140700c0b0042100d50241008000500150360000c40c41e4003440070054200000b84003c1c0d1001000b0b015201d20380c3c0c0d1000442e1f8183c000d00080c1c3c0304100c2c000d40603081d40109480404104003c032400c5c03080711508490305100802003503000c0e141d030884034104101842c2c0f901a01c3c0c3d580e048207048951404022030780e0b51040e4045800850710202e0b8040c81 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 187377715 1250 187376465 187376489
    0x20712021b06090904170403060f021c0b0a0501031d011e060509100e040305040503010509011d070f090c02070b0304051614091501090f0f151b0b040501180605060a 72
    0x3e0201058528400520260100b4000e02020343c40041001c02c940c01140c00403020445d0300d0b9114000300103544404003074102c01100c1041d888800601d44240400c0050090203105000d25110040d80a84141d5030040c844120600c0d0220754483e00307020b80e190800d407440b00303004170b417500707003040030032a282904000d009041000c10811034404c00102d41047c5e400c1c8850903041981c40c1c3c50115521f10550f0000d54165003001c041c8150a58150851505444a01c4510780a912040a100d6881e410f901c10b610951140c1c0a003040705501c1c0d0307030007151071061a106031400651140004009984260307000c48455010f0752040c40100d110703461a00c003807c00b00306010100c4004c1e00c002480540d01400c81506405074075498403640c0e020700c00c2e8000421050708021a8140c1d00d89200080342e0040c442d100c10107600300070304004284204c032000280007904d095020901c0086c3c031400415140140304451541d60b0740d6410000c400304120000c240f910418010620b45069401d0201d258010381c4030b10189070b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 187378965 1250 187377715 187377727
    0x1061a0c060c030a0912110f0c0f1507020409031706060a0c0605100f06020102040e100602030403031101140a020901020d080906060d110904030203030115180504020d020712021b06 79
    0x10001c90341d160000340790b225041d00ca0300c2d4480c2d036500601c942c40c80140303d0700c2c0710003500500c01e0304007241c2000103000c0c500395540070610300704080d11256488284d82d030080c4000b540b000c55203002640f802d2031091a09441d0b0405000b03901090032103072109400d40118014001c40302540d903c030f00c90690f005800f610b9650600c00c45000140c48000d000500600503912400060342010121809030010040960242c0809a5815020b4000d40c0640149c49880b01c5403800100000304404890302118015030003546002d00e141c5088480c0b00c003280c000c8840f5503c840c2480361005600740454002c0c0d00c0c035180182d0355881403001910f80681d6422040610003070070101701d0f000c0030111320141e0012041d0384600c54940c0500d81100180f0284440c607500018040500c014954000041c5059030b4450500c0351216140b032205071052411074103041c2da4000004028080c609042d0042c01c18180b51200141c01c045003603482c4450480e40041030001a03200c0850401c0d01d1306114031030608403d058480c145007030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 187380215 1250 187378965 187378987
    0x2708070206030604020904050103080306010914060d0e16060306050a060206100e060f030124080703120f09031202060604060501140313050319090302030c040e100504020a090e01061a 80
    0x40100100030384544008000156262101d8040764081c1100030020002982c49160014141c0c2054035040e00080801e100415030307254501c0c844440d0800103002c90f00b0a4800e8513000054652044510100d010388141c111207208640b4000e0094100341d1000b254850a1806205021820303910820440d8884800d00c01c003d49201d128000342d91903500040c64a5540d140803d0032142d900c00501c2d0075600c0e0100780445003082c0390710f0b803034042d420680c081e10b15036135445020354411003408080e00d180c1441c0a05d2004600a45000ca0a0784a505000a000f6520307251003507208040412200560031a804000f0640b41c030b03109170760240c007003420580301018200c0742c01e0740c0b0f902004140c41c4a1042604203807083c0403003041518008106080c80e0b544180392000f008220305102d00c0120b000e8400c2d8141c0d00c80074034160040c5200107010400805094041550a6020701000342040c0d07005085a07070007291283c41c0703010b02c00380300d01c000002054a5141c9013004407144084640740341c0c0c0f0201803065444403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 187381465 1250 187380215 187380217
    0x1180b09070f020f1509060105030c0102120306030c060408030d0f0204080c04022a071404020702091f030203060901021b0c03061b04051c060c0e0108070c0609050f012708 75
    0x80c21601c0d203080200700d030b4042a494050028040540e91080310311605d528158110820303c18a4058184c400716660b440c03d244e51212445050307409a00a2405c00c0c0c2144500000b85601a038010100d4542c85582030200344581d10581000d891a000003a40e0f58010f5004c0c09462002a881100bc40c030b02407409903043c0d01c4203550b840c0540719580002d062006564206481c0da02d1900f00f00e0300c0311042c0454806281d607070125114030181d42c044440701605c18a0140f0a4074076854010300408016525500e548009038000302c40306030ba940082001001507201080a01d01c1035031100001a40c034500007080d01c0c1c0c0b02040480c90400c0da44078251500c1a900c0105800b50807000081039014103030307071101208900f13004070b401c00d40d00100c90340091222040d0350900c01c3c40c1e080c0140340801c40040002c10841b00c200801148501240080c000300360710f41c1c441d44000404d14004c0400080d810410b94845040c0440300e0790b01c100c03583d124014407940c03c00d00e010418140c038451500c0c00040c08a0780d07408035a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 187382715 1250 187381465 187381471
    0x6030a030207170313080d02120a0c020907021509010c110c030a080307120905010519051308030a1113150504060813061107150509010c02070504050403032301180b09 73
    0x504410350910b00b59802041096a1110b07003460702980c0100e1b2109821035440400001750001440340c03007070a4400071520801c03104200a039980d5415030b00182e80034030101080240c44502180b06503241c91145882181820780903000800000c00c200151103c000c008615405012809800080160400d542d000034504074071a0f10480b0281c4955400d0804d84001c105200005c00b4a4240301501c001c008041d2320a901c182e1002d4102c01e0355078039152000080740d000b281c18a01400c02c90301c02c000400d03400005564007128138040400c041a0381c0d680c203607442d08000010030340300c50100001c0c41000c0d860b04d0000398020071031521030309103460108024181c01c005841c040135101e401c2052000e104040c0c00c800b001d07800402c1025030700e0f9990f02d41101a03400101001c0800b5150101098403158180100d44031400281e000f007401c18140b10410000b480060811400c2c950364078001c80c0c0620700d050810340c10400c0880c0200c17443d0714104010205020b090000c0424510b08400a0754a9480d06941a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 187383965 1250 187382715 187382729
    0x15190803160203071809120c050316060f11030a05060607020a0608100b0f030f2406031515120901091e050709021803010b09040804050607050309130e0606030a030207 73
    0x50404650b00201e03080c16050f8021450305181621450380a0040f9005030740c05600c03905d10902c807140010800c8030080002200140b19800c2001020503500c06071104251060203440c00090030001901c800003242ea20302d107000001d660100030044c1921440c840c103540a1020790b411072404685500155034902c0e14001d4034140401403002c6161030340010901006402d031541c980c0c1c0c0c1e80a40030214080c507081114000307020101031002410800020700c582e21126103810000343ca0030125410000a500002c0181304203003140b241d140b4036a5161001d6070410341c200c0c100d540e6030311081043d0209516000340484210f80c103080c01300e03001a0071384a06e80380b6042940c050b0108603640d841c0880c1040d60661003c00520300225040750320b41940c6440c0ca01c00c0310308a0080245504001c280030102c4e804940141c45181c050004000500b41071008210040c03081042d00d250030011030004a110441040e680c0700240d4640480c2c480c0070f07003007100c5e641000b8203e00410b070a001c2039600079596101401204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 187385215 1250 187383965 187383997
    0x20f040c080f04081227070302090123062b140402060706090203150105120105040b060f060424112d01060503120307180b0415050706020315190803 65
    0x9800d106065017691041100960310600609051404c1c02c410701c01200c41000422240f0403079441c21a00050080c00c903680a840449a03a1800c802c0d409070100451050300350450400501d030059562000520901482c1c0300100311200c034250400ca1400440041c80c041e8901d0510b8000041c40031100e0254020b40c1294000c1e565410b624003240500f446c2c2d403009400d4400c0507440d03404d0301c05220082d03040c2c0e841036032525a01c0c51062601130a03103200351405004400c00d0000b254190400c00d001d85040d4401034102468150386402070240400c0c446200a0346031495503020000640c070140d5410100d000700300400c0b049200700d942d154400800e8010300005000d070640c000c25500c003034000e00006d041c01030035500c254440718814059580704496050010f483d15049000000054070560305440400000b0741c105030800c042d410b486070107003024100703100d0240170120010395103000a510949042c603181340c14000680a025402d4038100d541d0303403e081940410f201030800001a00d801e01d40e150b6104e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 187386465 1250 187385215 187385221
    0x30a14010c1b2009090a030f02120403060b06041d16090608070807120c1d01080108071e030c080f010b0a0503030f0715020a020312010807050109060c0303110313020f040c080f 77
    0xc0156500520740c543d0840640c07010040fa07000c0101b4614485802919000038180075a4000ca84030114090704141c1d00606000900c08510550311014000c100a4405480c058a4610342c0d50f03500c1900c110020444452400c00c01c0c02d00c030400e5102c160400d10705281e81400d042441c040c00e81203004043c0390400c80d43c01300151603170784100341e40401c030004c2d840b0400c110700e40880c0c020190782c944e61115004103800b200c88450f82d40328407071460480b0301a0f40500380e142d05140c02c1c40b800c00300e184e04102900c0303c03107036001c00445c01040d070500c000d00300b0310300501000020300802425100c15590481c45101100d00411113620007100b00d42c4444440f110345940c2c1c0310035280c070b0b1100e0401114400307900741c40894401b00c0a038000008010303040180100c0c4400c0d0ba6607c009503a1000d050203114001400c100c0300b040b02a0059010741a2140701e42404101052001103c0d045508201c481c0600c6103040080c0c4429070401d01010034040505030f13814420280000c030b010b40f5004000e030034124044014800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 187387715 1250 187386465 187386503
    0x9050a090c0c021002030405091f03080a0c0506010608040308060102011a0103020a0324030318050d0b0604020909040305030a060608090601210b1005090901020a0e010809010902030a14010c1b 84
    0x104681c0c1c268004c060400c100c0f0902c80003585c90300700c1e0042074050317071100e00407882402441c02c40c800c5a0300e48440f01d0f984181560b64546060b04480c41417018405842840d1002480502010f4040c018680d6064000c0c50941801440302002904bd5070542e45401d800b050180c264400a080c070b07107070a00740541e0f212080e070800c4005044240c0d084a04400003003814110168103109130007102e029640c0c88041c03040100048c52408500d00c10b09900c1861072218800040c00000201e41c8514010001424103040c4404210ac40f04203c0e03007100065000001c00c11048000c0c4100b2020b440d051900b03070101c0c504004403d035a06070600a9103880441829421a0103400d0541500743e250f104070b0324840ca0403c501c6641e40d035031030f90188510411440c400180415030510903508640b00555420003482c0c0783c40010360380c01002030403608195481e24000c001680f410420311a03200c0c40341200d900001c98110b4418212000f00c1440010040c0322201c0716030304008a0304540c0125041b04081d485c22a100f50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 187388965 1250 187387715 187387727
    0x5060108010e090a11011701031104060b0a020613030c05061501030e0c03060c0346020702011715030a05030912070605030403030c02011d030703080f07091403010209031603050d09050a090c 83
    0x200c47d003079200080001000300900708400100000080c1c07000e01c4400d850f1020a400d0740501c1c11181c005a001d280014170041701032800c044014005e0070561004140d0340ca0745828a2012210f01c2c05414011411f4800343d640b51240e07600c0c14032544040c0c0028a90b4000083d158a00070780406040701011010a0f44000c80c2e1021044007000700f808254000d50035072007200ca45c2c44070303602c0306000a001461070540081c58000c03181810360594602c8100c41c81d0074803030300703404201030900c0001c00c0110742c03520f0241d02d00300402c41c0060b02800003583c035400400e003042040d800b2640444115002107104200c01608401500e400c5641810041071010311010120300414510710500d04008203a41c0c8142140d0703001c001002c00501950320000e00395907240039500005800d4908130b00044165404010340700c08424002c928503001000903240256141c002454411089004109030100c42d00401c10804104980c07034022001d8103081480a180070002545000b2a1081c007e20549425084c2c00e50f61040d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 187390215 1250 187388965 187388987
    0x10170c06070302060106170709060302071419150204050a0302270c0901030c0905060915070f0c080601080109050c01030207030e2d01090506180d08040905060108010e090a1101 77
    0x50103041d150221410300a545010a03c900004200300014401c00c84405201281c071900c2207440f18142e5504d803a4088000707620500066a04845100c5044504d00c4240802e80d034064203404040442840c500701034070500951440030400d50710401041006403940b84000040b00d8040b00c40d102d00404141400c08030000b42c1c0d5081d11803641d14020800740404c00e5018001c01d5100781d8081005030701d0b00740255106043c0d030081d142c1c42001030060200d54640800d810b031a00c03285800b03a50600d5842e590310540d2120146088404000c4080113101100d0104003080c01003010400034001103c06d030b21503a448004d4134210904041c2c00141c90024580604278803c00d100001e02941d515110545424120003100a40c200c08426552041f212943c85401c00c581940c2c4000e107070600c2c00d42d40e00342900015100303040340c6d50066840e40e0080c0104030035502800003008800004650b916154000506421058104074540000201032040283c00010200c800c50781c81950748000001050044e5a010b000f1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 187391465 1250 187390215 187390219
    0xa09060207142e080f06040504050a081c18140d0c030302090f0603130605011205190606120305040503070b0a0c1b0504090c031b030b2206020f180910170c 68
    0xc80301068075944c414030f040e109030108040138665440c0d100030401902d0f01501c0180060b8000c010f4000400d500c00c0081000010741005002041082c000e10825a583d48000c8031140411840c000d05001c1e9028000308800d1020018080140c0c00e070f00c02a00c260200d50000d0f042540c0803942d1031064032041011030075441d006002075107a240092078a081003240342412243c0c0390920000050303031103031400302026241d440f5028010100703010b0b8508140c58000310095030440e0f21103074005002d05c0e00c004031a01c0d9a020750340f00ca6485007840203052410506504c40700140204100307031503071554071000700c81103564443c0900480000c008240001540241c21090b80303d40b52003040c0042100703640415044074840c0d0b04010b803d00d0031000701d80001e41c00348409012500c400000a800c02d48a0350342d07000981c189040c01c0300c1808951248402c0741c024540c0d0707042d0034100151100066903a8014405006005c4a112130145072078905005102c217980710f0503c1001c90602c2ca07000f64070051211302e044241c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 187392715 1250 187391465 187391539
    0x70c080d02130906060504030308040203072d150806130e100e0f01050105010e010507170301060c0b06090712021305040f0c120b06030402011b0b0109020a0906020714 73
    0x6000d100080d48100308441040070001d40c0051a507109015a40c11624640c4900f403c061844d18165080c80d40108100c1e407500801c180401e5448101d2029120000840004030108190714207103921171300650040010455040340090050740e10040041c1d0010080d104111005107044c40000a807440080d103202500a07280501c81032226070f48032800051084044270f210500000b41c9500700c6200317001b0a8000b50000014200c03550041008000c0c0c5031085c0e502a0250146403035691480d0004e0300002d0024902450002c14055942d00035034014400701c1e145441400c11400107807003151403411080d5840d8011070f1450010602c1030001c3c00511003c1c2052040c0080d11440c0344c005c180d040103000109090050070702c0520501e10941d01056000350802e403450721a070300192402102c048418145602c2501c403100051000007290b402450194400b68440740c50010281000d1401e8000004550007440104113000e2181c00e508a1114192114204040c030b10100c50b620f1030303101c4159040b03024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 187393965 1250 187392715 187392727
    0x7050a0b0f10140a0b090604030503160312180210050d09060e0f0303010612020906160b0402040501120f080a090308070f051905060601110309040c0201060302030c090405030a08070c08 81
    0x50032200360721400892106440745910f0303000001582049600580c0c1000c13403c401480103035081d4004007543d420040442d0309095903641c0b490300e10382c8038000c1452140c00c5d694120b401c2580014001021b0014510300b80020903081e9400c0389070103840f40020384580000850048003902500840341d03e040350320814400c040040c10600e000e0000700c081090a4810780742504403c1d403000c02624165142d07990342c1d00b0300e110100b0050000e0b40091600652100c4200100e9402503c8400d400300071622882500e00300745403030700400c41107501c164000c1190303401c9031811000080000035946119541b00d030340940c480c0000402141e900c10150002013140307500141c0c030b0741030010b202d0020101510a40490740d180740000014051111151001000c1c1e03400079003c2034184d13010742215030b00164a0070031242040840c60004050b01c0301c045030940540d569aa0a00a504041c0103002603640185e03005215030510360307502580c078803e84038480c0c100504c9101061240f482506125007464000c0c00c0ba44d1114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 187395215 1250 187393965 187393981
    0x90703090201030b210706020706200709020a11010c03020408250f030c0e06010315091808041d060301050402060909040305040305031201060f0905010207060e0a0f060c03110313060507050a0b 84
    0x1d0300b81d060417842e206d61180003d030380d44000b949030309407207080c0c0d1044103c464050900002136250b10314128079000d00c21003c1050f001520240c0744080c2140d854256540340058003034215444e10344a0810103004000c18003500200144c9072402c1d0010070701890f100030400e1380344040c8181541040011b000070003000001d000040003c4030940344600d10707070030080d103c1d000158108e40b04030b12070a581100e198400c100d542400c0d4801107a48560fa0300920307862103540c0e1841100c2c1e00031340104184131600c07c90301d030101d41101003507588080705600030490b80c14203400050041c05188800c0d13219152590004080612810584000750791180072203840ba007800c11100d80042007401503600007081f210486100c64400c40c0d0680460f041038018041c518104082165200003208082e07410000c0500c001070110204c1030303100028219541c0309801d100d03945c6001060034200c51143d4040b03506c1441900e4a4920808000d03007120b0300c0e41807050b61118035240c103600b40250032401400c6002d8450070041d4417 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 187396465 1250 187395215 187395259
    0xd0801140a2310030b090c0304080c0604080d0c05090d020f010c050604034e02090a08070302010e0108040c06120902030d02070501080c040b030604021305060706020a030515090703090201030b 84
    0x3402c4111040407002c141d910301141110020324699a1020032400440c8020b001103005641041c0201c070340500d84808003020070b107811010380c0d04075201d68000414403d0040d0324411130740d10303000e80d05c0d103586841d007080d001502550306408040e124208401d200700c2c15078058200c400010381d00c0400e944442c9041d00300a0928031b4110030101240020004c8140041c3d802e0f40c405821f0604441202e040c0b0a540e843c0c11100f85032210080407035542044401c00a5440226480007020a0402040f01600354400103003049050840e40d814170441c6c9050000040d030464601c0c040e038010b46000130072000011740e0f800c007411543c0d10294140c001c04440d03180d615030104120003600c40130b8850000c580c4818000080a10a034410314420200501c0414440d1070280c00419081c45d580201c2890a0340750b034001420303030344040d501300c800d203600103a10000030743c2501a09921043c140700c130150071b460540100c0c50081c001806481050380d900003240031603004e50300a001c6500d000e0b10503401c0e804c6c50070350f82d03003a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 187397715 1250 187396465 187396529
    0xc1118040804050f0a0302011b0320030436020903070315090303050c03070525020415061b030e01050702130f0e0f030c0706050d0608030f030403110d0801140a 70
    0x10425168141d503182805c07900035080702e038181d407051034540741c2c0151894150442c1c0821000c200b160b036010403c0c2d86004d5241c40c80d480e00b07030010310390717a5141c0103e0304003020040d54422400b50200c01605251022124200b0701040007a01c050790b14600480017904004554000400302c500f01c90392180041959840300b14114401e4400b0003058440d901140740c18007084580300e000903c2048101c110304d8500706194900d921039100c460015040d81e0004040c1c0d444038030703840098810180100f005a034424910850001d24483c0a181040c0030384004200d10041c0c40c1e0301e4140800040c802c403c64444403001010540c1d140010042500414596805824883e46840d014840c07443d04540700c903404000c5600250403000201160743c81c001c42603800d90444a090380703607660b0310000000c1c0300c14140014243d140e60404283d540e0715051801030410081c809550815a00c070038500d0900039044500b0505580012004840315022540001c0c46000780c0c2d000354403940d00d08100000110f03080444202 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 187398965 1250 187397715 187397719
    0x42a0f090f0f090b060d030201061d160804020105070b190c0801050312030c090f0102030c0106151e090b030a0204050a0e010f0503060702030405101b0b07080c0a0c111804080405 78
    0xc0707142e450005500351440d10350080c20b0a001d51020405516081707050b115010700c04d00001c6051030f52013049c400c078860750080b100043d03c2d44008120300e4200b1031092a25040050400f010581041e400003003032405400340080020030b41c0d40c0401c13403c005540c40d0045100244c2c03018400050081c000070200d08003807103920b002e8032500d00d5030b40c1c2410180e000d8034451000107100030309002c004002c001a600e40c2d8140d66040d40401c00503866101000e00499002d0000c050140101110315040204040080d48000c03290f00d40308a1303102d00b101d42c00f00104044a01c150403464a0340c492061600091096074405507002c194001e001482ca0409407400341200e016140040c030f002d68420038151038210443d6280c2c0140c0003040300740090b00c1c000000c882687c2a07407410034075600c82c07170500440c0c02046000c1901c0511038141000b08440c1d1100350198024400340115040401d40c0c04003624980552200030075101d15002c41d003c403500c0d0b024001d1132098021400420f80d040500b8015000ea0060080324 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 187400215 1250 187398965 187398971
    0x1701090308100302060d02071a010b0301031a060102030a0809160303020c0306010603020a0801030f06140c0306090a020c07050607080f0a050301150503010308041809060e03180306042a0f090f 84
    0x601c2c5164800140d5040b42e401130301d01d41c40d217003014407803000a60005204440340084e10446205659000d0308071806080c4030450f00360b0b25410b604008a01d181c5d0303e0070500380c4861480410503143d9021042c0c0d068014142050000703600e4100b0041e0409403a00c04114003040141d400006040e4001010004144160251403803662588021000c6e403045080600c089080d0701c004000240941f029000b105000354400200d41b2100020769022020944a960b040040803081c8405441d0402459800682d094011441c0c8403401504584440c15403040501c00c0d107001c102e00c81400600c034100ca00f40d800e0900219a0b41c031a150028115130401c1c0200d22005003c03010700203d40c0e0040f411030381a42c1d00600e00790306052500d0300703034510002e210010503903071511000d5000000744513000342414100040e001d191140c0d000c403403180b001a048881c4900c254030040c01d00010070114080800c0d02c4204001081d001c089408515a804006600116020009200010b000d40ca65407041c100c01c070350b40c1018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 187401465 1250 187400215 187400221
    0x5030a0e1504080a080a031e0f0c080105030d21090f0b1609050d031e081801051003080a090806010b090909010b030d051804020f18030708030d0b0a1701090308 70
    0x485840c0110b00032200f032940500405800b103403441001d01100255445c004c41d4070a030402d441a0701521403d04130090580310565036042c501c146c0240c0116118918107201950301d0000080c2d40c402a500441040c401c071b14240c420001a50001da011148031003078280408051031401072280c1074401743c291103852210011a10000821003c507984406907a030300710105d42000d040007100255480c046044c08a0400132181d01d600700c515240d0007020319100c142403494070900850a107001242d01c1d0303c403a4541010000a030300d00c108900c06807900940401d4450708040c6040e0f80c403140c16002a149485035a0001401201147c010501d0310400c4e2180c00d41c82d00c2e142500f40c00d079000f5001a0b5455000355004040c00351060000d003050095114005000340084800b05040341d11000e50b410410400003851145150a0210801c00f040140c0082508500c1d0481e01922030054000b0070204548401310b03ca80caa0354008240301a0048248641c603069111000e98000c166180c022404a0500000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 187402715 1250 187401465 187401499
    0xc1509030c080a230318010c1a0708060a06091202010c02060309011b0801050f010e0a17070504060614070f02040615050d0501240804050102040b0403050703060509010c1704050a05030a0e 82
    0x340000c0c50b140000e60500695600349950001c620091b0f0703040006100008010412150b101803c01c9149290b43d5240d050403031000b00982402043c05019114914080210960094038682202d111a41c1c0340d402c40243e100481345d80140038400b951040f000320906c40140c074103500000c2c1440c00e0038006114000109000d8032140d4003403080690026650031019038031b50041440e110300035002070140c40c040e0b480d03da4003101c03000c514000e040b182e030000206000600340b0b403007900301405042c10840c5120b47c26000e407844e10311513280000c0280d4010980b00d011519035801c84c1e8040d0582200401181811901c020102c2d0018589060500e041c140005803400c04000e0111002c91400e035104190051f4a900f6213030311401034400c444940d42084002a142ea0500103403000e98498405003402600c0c6040c03610650b5005084070300c0c981d151a41c10117040d45c00c04c2c510484100b0000d243c50080d85e1307505042c1e04140c0c07089006045808001354500100354800040c040503001200c10100720742c0c01c0300b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 187403965 1250 187402715 187402763
    0x10080910060b250503030106112401060c03030905070e150a06050901031112091509010e0304030f02010c0203100e10050402090c09280f120c1509030c080a 68
    0x1154180d00c0c8000c10119019840c0803e0b00d41c0c02c0d090902c410400d0a006989851640e80309900050028085140f8480c0600c0284200400b0403088201221041003014994030700f04018070504c0107025a0803003400402d400f0380c000501c0a6044410780f040c0f00d0b0b0781c2d11125031803041240c020903904480d200f41180c0e40f81500d641000c0d00d0380c658071a402c0c24074a600640042c540051030030b48807a03081c00341c0c3c0003610324214603900c9242c0d0345001d00b680c80110f14001668000103402503007141d0400e8210081403000009032011680c008142e0010a03609000503140c0c02030549019406015100b503400704600b07a6008800c0342146c0008442a044004181c842251800d680c000c0d80080d02002240a4141e01405459031000084c071031075240030342c211040341056007403081c2c1e0b502512405040005c0700d82441840010500b00001100f0000139a4aa000c149072500031440b42c0c40448024600c0980304600303240265a220207241d40c51074407000030a603100007019040301c9524104514200e01d0386551 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 187405215 1250 187403965 187403969
    0x8040f170d0206070e0f0d0c03110a080d0e04110d06030201110a02090109050406110c0a0201080a06050609040914010204090e01060b0f0d0b03030d0c0c110a0501050f13051008091006 80
    0x9405001e83d500c2d07a40e02210100c0110009660000000c0d4001a0a135107080c200520103200b41200780100c0d18616101c00300b5010301401610501c1c10300010440c0c49800310f4041c000b00128a44803801000310740c0008c00411000144035201030004c55440e80c035800c0d83d4015000d89000b62545202c056500d00216078840540714002d4000d50104010001c10b10b0540260f0f03000740c420040401c200b6540c0740d9103542a0880c0f462426a9444680c3c00b200390350700800c0303698100008039000e00102d4100004100300d48208035090303015a954038000f006000c07008805c00903007103000001703641c0d455807000310070060407981d820364990354600000003c2c0c0907141c1c403c440440c000d043e03049080026000c5004010f110000000c3e4250001b000704540d820854494000549160380340c000f03182206081c111304e442d95600c0c0c001d0003000ba0040502c4180e0b040300c29a20594591100c1ca595200429423140314211290300c884d400050300c016035840f5070b802000140c45081468215610150f291207a901551114 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 187406465 1250 187405215 187405217
    0x80a031d0706120f060e041a01150f120906060b0901090b0307021e0a0501050f010e070c151d0607020304080d05031b070201021603080901020d0e1e0a0308040f170d 72
    0xc1640c80b4408495411451301041d0b1340d600001c00d00d954002d202e134005030440d030450356030492080392001c008110701150302600c1c002107280035120640310050140c200225141050101200540c1e40c0400c1d02c0d04040a00d50703000800b400042d542d2006000950040b10009000c520343c0c200104104400d1403e40e07201c2c9010794003c2c00c100c00700c00d4080c1c94000c0c1c40c0711010454002ca080d00b4010502c240941c03801011380740c0ea500d44640c0340822151503010b001d0301d24010481d04032215000710f9840c52030701c03466060030640001d03401d034207041d00203041d04805c11000700c6000b0041080704040e00070025104131182034081c1c07201d0810340b0310102c030984012910006a103078041482204031000b8809840680e00c103004545030403160540c4581841d21070303481110903690004911080b075a041c42014103029084c01d12880708601c03a400a405140c045940c2c0808160000000301030369200d1081500641e00b00c10300650703c50f05c5034a0030280d07000c80e0242c20760302c143c035211000700c0e030400241206a40d09a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 187407715 1250 187406465 187406477
    0x70209010e1b1215040902010c0303020c011d0c09060a030c030605040c1e030c051c060e011e0c090b0325090b0f07050105130507150c080a031d0706 65
    0x240101d0885609000e4034281103103910750180d00a1240000c01400d000300c00d00c9603802c2c0c5180038120a021504490000d60013a405d04d01940c0050f60820741c00740c12280d041c04c01685940c00c0344c0e4031500500c100c0c440301841c80307500b0705204a102c4d4007040032440304070252951105c2d59100382c240610110948001045400002c204002040c07460b42310b160064030401c060003200707030b81d5a001d4084914611802c490f01400040400403c5001341031000180015946403028030701c10f80c1c10100014002d00080d288a454800c4407000c035100b903014000000c10018400b00c0203200c0d054580040c8030521400e000f041201d2000318000d00c1c01401c1e64401c0e05440014a58204c0030703500392130407510000aa000b4005034060220340c0007520400380400c1141c0ca40e08a485540e02d08119080d14409080100d80040c0c0004182c0421004a1075109440000c0d0030001c0804090008131840809144c000e0040a0003240301646554180c01074281a82005400404a642c40c14029102c010921550002c102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 187408965 1250 187407715 187407719
    0x6091e0902061207020609010614030a030302090a0f1d0703050c09040b01020114090d0315030203070b030705120117251205030f0d0e06091605150903070312020f0307020901 76
    0x802600524545440070b0a02d504002007800450446101900c0345000740c3c100c0c80c100900c42d98244150401003401201c01200c10000d000441d4440380c2d0044041c007050740000e025245038480c0120000103001032021400c03429600c003400da05821040c1c104403144104a0301003120079100f802628014a0202c1c2200d181c4035104007044014030661404a0555480d403043d04295a050700d0000d12624928000d0855454000d40080445000200440000c00c20030820700242c0c40c0090350700160351403101041c1e902e441ea0f0740c00780c456001d55003000220764840400840c3d00c0c070400d1041541c44400f03c048420142000100c1c9280500003408403081800100d420010803000340d02c11072040d0b0048054038a4803442d1030881c140da44c807103150001615200c0d042c12100481c201300b4554808410f00150420b003c2561000059a2503481441d100d40140018241c410329403000700d400c0907100504540c030840d6280342c203811002c100f8070000094001e9403403000c5090004805c0350041503008080b00c0140c1c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 187410071 1106 187408965 187409021
    0x30b0102060907060305070207090c091a03070e0907030e0114040b060109180209060f0c0f0105070e0f040c0c081318090506130312060b0d0609 63
    0x240c007100030415500d001040601c01d40d481454081183d403100e0074100c1c03400c1e0054000c5c0d9603552070a08449402038101904404442c0704041100e03615440d040340d04198002150000045800303039009164070315111103c036910410500700007441000d2111010701310f0b03001586500399032901c08180030500090b8090507611410034a010801681801d0800003000b00081030320040a4000c51240e09a540d500180c40054100500c0691a008001c0b001a9140c0002542591551a181c04621507501c00d80354010b1010014024680c0d094180301400020413000790707102c04100d958000d0100182000c001001d5a5a100244010241c1007a028040c0d018030003895a00d6545000b8400002800c00320381ea80c2c0c01080c0c03121410b00c0207500e0074240c549100356000d11012501d05900426030580002c06000c07010250b10003000802e8507400d01c4001c40b15544c03030080300712002c001c10f402c01c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 187230215 187410071 := by
  have h0 := BRFrame.cov_init 187230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 187230215 ≤ n) (h2 : n < 187410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
