-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2349
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:26:50.313962+00:00
-- url     : https://prove2.me/submissions/4ffa9634-10e1-416d-b6c8-022d3be9b523

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 422302158 ≤ n < 422482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 422303408 1250 422302158 422302213
    0x5010915090b040905030403030507050609031e1b0d020a060e03042711040b09010f0e06043005010509070f080c0906010c060e0f0d0305010806040b04080418021b 71
    0x26144003010b02103030103441005805401448005000801c050740440100350030303400791042d105152100340c0043d44a00c11f585105404100c0113403c011144c1e10400103003003664510b01c086c2005402400a142494045600031015030000d0b14204140140d5015000030855a03001071440c1c5810140710100f0403500c0114030449080d1503001030750300c0711260f100c20000c00c01034002c280c503941c4d82c01030308030319600c86142c03940007d0384a414030007602e003d818503c0c500f40e401001c00b41014282040c0c0c0c05031344401c44900d002c00300c07002e050071540c0e564410f40088481c0900d001240a1800c4060b19240951640c84110700712140e042c00c0008940200f0b2540040034200c0d101001900c811004a8180c3d400303200c003030304942c9054400c4495900008600c0540050041030f030309000c65a07141981211002d100304241a04206c0c0001c00142a00b43c913241c0c0540f003024200e08280c3c582d001d581c0c2d4030303014600400381c0c2e82d07000030710107070f008401c065041d03401c141e0400502c0411100f85110f0000640e81904 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 422304658 1250 422303408 422303411
    0xe0d090e13171204110f0105120a0507050d0e03090a05090106050a030b0a080312240303091c05060403110616020c090a0b031002040515090a1404021215040501091509 73
    0x405003107a96082c100c1d290090705156604181c2018100341d80301490100d081845100000d82072901540a00309807501020a103550f141c2c00d544500c5004081c00004003070401b0004200329505c061030292042c1c80c81951210001d5403159100c00500c10200042c5c0c001d640b258019000400ca0181d0000459611001a180100341c0e01248070201c0d419880940061081c0d003c040b0b0b00c650f8050030248203601c9001c010080c00383e0309600c5a4403c01c44020340041d1a016042000020f1060900404590a156102e5910184c0c1145900c42d10309001c0140c50850006a028400c00190041000b06542240b41c07034200c0654805461406581c0c1e0340009c4006008850660000e280c400036540001001d4002405440a030382c3d49461900080d03002e8040d1a00c24028808440c03a600c04040039141c0010002d000140c0c918201220303846061420300d03009510a408200d10040101e03a564202c0c0206064800c1d01e4411040b0010041507a4050300f11249042c40c00300c80b1400d001d40d00a0807000c076005140e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 422305908 1250 422304658 422304683
    0x11031506060a110a0f0302100c081302060309160e0a060806150d03090e0106050a030e0111030c031015080f0a0e0d1101020d111309060b0708090409060e0d090e13 71
    0x95604120131054054602c02c043d6004c60103064000c252070b00103145c907500821210121000a507045a402d591002c41c28a4081c2482e0050900500441d04422003404440307a038001c0c42a010b5811040e03400c1592064120b100340308400d105806904060035140707000e88914035200c0c2c1190741c0c0030450404c8038401d266a04180f0705041c00396a20a015200e20308040c24150f031101c2000c0c1c103640c0420001000245801606e880f2220184180b0722a001c54002c02c0d8915114546a0141c83d0400f510405480320030b000c0006001102d03004440d011001038031002c42a00e0400c4510b01c018000408011081c2d041115107409800d000c41c5413500d5544a003019042c02652014842c028040c003000070f0280c07031a00000d869503540110142c45621240020400060f44a000078015140148900b03c0c05660134891800003c01c2003014118440c0302400c00680c1d9109a100d680940f005541e042c0b02c20381190120600141e4031021074030240a41e00c40c000c0890419110160007402003a00c0034020008158 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 422307158 1250 422305908 422305937
    0xa0e060f090c07050a20090c030403140f160303060e090a0204020c2d0c01180b03280906180203030306090c1b07050a151e05090d11031506060a 63
    0x3c2d143c0440d0801d0485100300b019140c41045c045d0b6064103039112406860f00810f00c1d26010304680e00c1840251400d0342583c8a9940070395040b0000a0740c403504030810703c0044011008071020b84212103c014004c0b081c2c20f02c1c0c0c103001e400c039030320354101491210246081065190000a800000e2030b816540103949200a102c041d08142c1c00a074030000c00d0460740c0c110103032111600c0420380400f04c10015280c07030f86482001901e4800b44000d0743c6c58221039032803080190b12000c00140d035101848601c64810000190002d100740160300e00628604c0382d5624002062101c144125201070180704491000d000035900000d030390340002008144a1060b000001e03400c10700c080155100c20255404c15108810114143d589500090040c24021040c17460006106000d41c8004140c80145496021900040036070f0051125401c210b8041400303004c00100038662904c50590a400c0d0091034100d64844240c01018100301411680c440e445c2450014010255a01001c40f0340702d041500380a60300d0707100d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 422308408 1250 422307158 422307181
    0x7030c0507171005130308070f09050904050d020c030c06070215070606080a060c050a091205011d0c030709090209060111160303050a08070306030c090911040207030c020a0e060f09 79
    0x3600109881c040d42202e0580030b000000e02e11208060102061200c3d40d1605030004042800100113000200c00d8004500c0241c0901000c035205a014a840b201d155100c002041c1c4513030b03040d6000c999650040d0801c001e01941401501a0920308401420345665054000703281401201e1021f072103056502004840b88803914115441164440d50600c0341c0c81d03071580c1094862400075025503949003824020300801c0d2144003102e02c003031001c0e216040c680d400d0411102c140c0c050418125900d641e0b4888003a0b0035440d046158001d140b6040052000780c00308014581880000d03840341003001d04042003100182c1d2192115503006c00b00786040c103042c1085440031882c1500a04842c1c6a902e452030020007415403100080c000c0c1c3d43c468640064548607440110211440d130300c4003070820000480c040c409040e140e0094031070680505040145d0200c001e0006080f40c1c40030504070046003550000310704500344556801c00411207d001101c007031600c0004503413101088254075200b540d2540021301d02d080d92 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 422309658 1250 422308408 422308423
    0x60d0c14061b070305060c04030506130201020f250b030903040510021e100615020a0b07050706050c030702070b03071202070303060b1c050a0b010e04180503030f04060b0603040807030c05 82
    0x1000c01c146041ca80c500820740300c0c80c650000385c1300d03805a0400a0122080d1008507401c44c1e03401001442c40782d072454180c01c600d4809100490440c0611030050b101c100c0200020304040c107000c0156038034891024400c245514860340710305e1118000f4010482c0400b00401581d0031100c090b41e14000f00e680341c1c00c0490810304610139a441e81803603642d107248011400241b8200400601c07208125464482d010903820701148044880180d0212002e02e00191401c01450b8000079603003005070600c0c0f07240d542c40c410f844080f070b021003c070384000c010011070700da04021180041200c0040d00b071440c1810395005089204104a021000d40c00240600801d40709511803401084c145007050307190903410380d00e04070060102586969040c2000701281101e8824801c150f00100141c48003100a00c0800a00010780b01000c080c2c0d846120420b40c1030701184060005512414582081070402c0c40c03d032510600300e64480038001e005000c1070081000041c5190112108141c0500307058400c0e02d01e40c0381c4036180050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 422310908 1250 422309658 422309677
    0x40b0301090c05280b124210050c012f0705070f120c0f1d04020d020405010314060a090c12170a02070503010f11220308030f010e060d0c1406 62
    0x25280009200034415021b0f2031038150300c000c00c0850352140141070f41004035508a6900321807200c9030301142d164942c02400e005c2e05020b482c10261078502000210f48545580c1e042021540009804417014001c0c810000304100380c0d80c1800407540c4048115184405140001246107000940300c014400104940001403119092003203845403664004040c0b41c0c1090303012190400e044001249685102640ea002e803001c00c0c842134400140c40350034180d00b140c007400a0380c00c2503500100f07802513112801400e0196003e1041c440c61500c5542141d850b0000003890b41c4001454498902c000501800e600d1041312400c0c210a241e070310707290a043c0041c012601c041c0c108160000b90a14205402140f28402c0b207000b10006c1004038030f030a040a050354540d100003415100f003000000501e0f120340d040342d40c00700c05001c841c4000030748a0b075031184241e00589800c0c981003404401080f0650012404990098080e110120020716940d01c0340ca034002c00b40152101d01601d2040d6160030340f034039415a425800c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 422312158 1250 422310908 422310979
    0x30f0509090421080417090103060e0709031506060203070215160c050102010e01060b0405060c031233220902030a060c09150e01050702040605130b040b0301090c05 72
    0x90910b8080440c0d040c007803a03c410340c1010100c0d0743c80c00d0b0046401c140300d6500010015101e44801005d11110741c007240300c2c07906240d901c8402184041540540600c1810303561503207400c843c2036052400340b11300c0f0070700d1620340203003082c0051201d40d601105a4000c1641550b09a44040c103401e15a0812701824280c820ba05903014441c01c140300c040c0e5031420480c0c40c2038008110801e00810f485090380d44600660f111110108030801190610500070301030300492030192400c03c0014002e2135541402950000e80304030b06003006c15582e045021019064500d245c10b2001c00c0f00450020074101c0001c255041c845440c09500706000b002140c00c01c03040c45a00900350303000840c081c0741840003404003086000006080d490b000c80d2500420b0321102d03840301c054440d41d26862031100111099808000c040b07800c103813114000100c0c1e403904010610070301e020b401c0100c4e540c0e2004050000321000c0c1464544203a06081c0590702184d000c1c0750795401c0d030b501918131840e0805428a0358071058840c611200c10701 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 422313408 1250 422312158 422312161
    0x409050a060501140109050a050d051e07030c060306030f03080912040617070903050a1203110a051b010b01170408070506070815010e101b080a170a0e0a030f050909 72
    0x22079010b0b42c16a00031101800a0414010044403208420300409400c5581494240890314010130b1001d84a4418000c0354001814140c070002100302d9008480c8803a07000400500800c00c450b1203c4015240514041181c50710f16201d40c40785915180c00a01070260480104941a41c288445002040c812910a07a5503a83c0e00f8014007880c400c501c07142c07100400384049010070b403041e99200300f00e07900040200b90014240d1600e000c42114041d1800600d503540c407060015419007009491038050f40c2e180c01e41c82d280e154040b451800050841a42c26900d0315031000d40c240c1c0c110703001190301e0100005c002055900d03440c162110744188940a0424880c81c1e080008036988074040522400120b00c0f038020110aa41c015103220241020145d440311584500d0704405208000d2200b00d5a10761700c00c1c1c40050240e80351416180d204526080005507410381c16038008070600f1a05402c000c0003e020022007641440d0240c840c6001c00d0000d0030011a825800e00040c4680190389400800030540000c9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 422314658 1250 422313408 422313413
    0xe03030712081f14090f01080c0618031606020d090602100903020312010905181513230f0f0a1a0618010f15030e061513020f0309010b061603030b0409050a 68
    0x21384004820034824940280055011007070114428102e4803a503000f08207144c109410021103030011101d00d00d00321540250740ca0195001c01c1030030039685c81c0824035012281403800090070038051004910501403083c50801040ba4009030744d10114440300c0d40001e209209140c201c2c214130030083c09214500000001107090080c9503c0350b80102d910b01305169a0182d01d1020a031610704803140c90341c2d400d001800282114001c4036014901ca0700c1245140542c000c8000003c01c902e035a41c0214142e035002c0c006d10083c1c15420403a1200c040c180c0c1c0001c4c000c0010580e20300c130708050002012031025210401082d03c58441466080c2c0c900d80580e00e042d031640e101d40d100440d0640c14461004021260b51107034040c1800b078800c6210007034a801c0a00002d5561034170104d002450b00414a80003448510482510761591019110f01d0700c62482c000d9803401d084404d41c2c2910f801540c194030411003000101c206498110251402c0c6078507090220301034560b000060010305035048090000c0c011540f29104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 422315908 1250 422314658 422314679
    0x5070c0e060a08060106020c04021c020706090204050601020708070b0d06080717060f04021c03090801090f0209011d010e060d0c03151a180603011512030e03030712081f 74
    0x200c0d0070182c550001056884201035652070080c41841c016820034800d202d154246078004003040306481c0c012044051340502c0c4001246d009940a44c0d4070b60760754a50b4011841c06006464005800b44002d21645040c003a0003078403020381e84a45101c0030000114103c040500d43c21044c000c00080003914640c950316403903002112501a069001400f418001035458070145104070301480d00940080f1240c0c01c540081941303420202000e0b001c3c80141040003454a0013401307039100c5988540e00b00b11541a040c4140400604107130010300f0860050f005c802007070b4500c903508504551414500c501c00380c8556001c540c4000d002d8a0240120b4481d09021050184000390f42010b0281c0b0b610400c174000c2081003d00880341d02c110301550014251f6142e00a90080358011504030000900028040c02d02e4000b240d1182520340c010031508418080703003c18140c008208006059080e0013943ca0701d0b050703542e903080d021816038100091000400120310b154a80412859801440340e401860190307c0c2c019244 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 422317158 1250 422315908 422315911
    0x2001060914090601240e190b04031103010504030e0907110d2c15070c0e1006091403030703080910090b06190308090f12010203010b030114030606030c010f05070c0e 72
    0x8140f0402000165070350000c0001402041403400c410911901d00310203ca0111100b0803c03503009881c1426890801d51211a410043c062040011358403071652401507103403e542c8201e1032107645800300b040301080e045100890004000c40c1c58441c1503840d903100b952466058180d0107090f11443d4a49054283c205d02103a50100d503984002d0392561809000c41182c03a6200f4941d0380050008104a640440d00c20103400c085108140701500c90b40c03900046048114100d5010000702c052520030429240c111a41c031000d000070a504050884694000c40c1d641d12030100018200107008000580141d000d00c2544581101c84900b4015002d26050040400009442e41485080d81c83e54007020710a03d80b20b1141100d5010480e14240ba01403400c102001c190041e202c0d0b000081d448194000d00300030700c01180a004056082c035221350600c240d803607072100e0002c1414080d5105d841400413507034000030120781c1c010092134800c58658509038212241e014810000301400c40400c03000c140c0c9451501c185 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 422318408 1250 422317158 422317171
    0x2150a02100b030607140f1608121b0405060a120510140109030f0803060102010b2706040b06090d0809181605120703050405070e0705282001060914 65
    0x20b02403444041c04150320b0326010b0f15040701280d0410074410142003040b004e0513401500e2000c450411944001d171949082c90b0900464444d40001000641d0141c803042d0303141c1180e9a03020320700c003004d41e16698043c1032160b030050074807401001c59007500ca10310407142c8a880c04c81c00c000900c42403c140c0d481c0500c0c0704542c008d00d1904440384055440399480f42d40d0a004882d04084010900c3c0d80c00d407241c1c03a0706e0740054241030441d500c51709032002d591a588001100da226400c00c900b024038042c010080d0176500640250310a80c00d20941c040703150b550b081a105408000c0b00d0480c4000704900d0070001034811540c2c032581040e0194034010700100c02c030090900ca200301c160314001c5420070a00c00c0b00c4505c04c0d0010740e0741540405020514491095025a0740f2601ca00111440a5110203d01d840302d0340c100d0b451800174100107072a00c3c2c04c1240c4190b611910f0702d0020b80001788100c042000d412503454030035181203000d088552417030407503094011900409100c1820080b5030700d06204d07540c4032081200d06 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 422319658 1250 422318408 422318411
    0x91902070f150606050a0e0112060e07120b010507122f071a070f0f0510020f0a030b030c06040603110708030a091e0c120516230303120f0402150a0210 66
    0x5844c0c0d0140d800c6844012084e030711180445c214170015103005000c401c4092409030740354004660445000b013128012502d6881d040c1c40c51071040754003815101c1b0202e10074104501032048a0001e010032041e03211549041c02c0c074000c81419110203c2c407005010a241904640c3d008155014002c04030f03003602515800ca51500901e40c054108402a10030b084000f0030802450f0100c03004540c03600e071007e51a1348504261008403045440f00e0090341c01c648134501c02c003100080c503070083c550140b05001c5290700940180021110400000c4c0c8035000342d20518086c16110400788400181ca00210b580c0c65500c410140e0700e904000c240100100342600e003c440300c42c01c052204035403901c285040500c0300c0d8070400004621342010440715042005200407036182c40740714400407280040025a40c0500150307900136007072401615110348080e031308510190081d041001060242c04c54510000e9001e84c181c02c3c2c2c0f600a4a4a20100301104540340407000090004a038000c00c16038041541e5001c031090490 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 422320908 1250 422319658 422319671
    0x503070b091923010510140a120804050906010e01080f2a25050a0618060c080405160b0f0703090527180604020d0c090c0806030105010f05091902070f15 67
    0x102d26003282c0c0165440000040741c1c1c14200464107c003030144022104c040c00100c80340756250519001050000c000315249034011500344503905007203a000754000001d2a0805001194000103040c511020700307220343c4c440800000807950b90202d01c002d40007203020400c0d09103c01c5038014014094101c1e641000e2080202e241d031100b0080031401c072481d019000806802c485100d41d5541000b8040d0340d00158215004402d0040800c02c503200710803030915035446001103842c25203859400d01c10201441c0c00742d501c91250030310020f101101510401c0b205242c00c16921003850805441500e00d540c4026880400d06242c6a0021781c1c4c0f41e5000c2400e8407034425401c40384c40c0c404056850040d10940011030351310000c00107003d8035101d0201c04009000d13456011010341c071900c1d80001e03501076030019000706030001c0c2401600e0170300f4410140103080b00c450359500302e0300700000950003050240064800c83c00280c080300e46000325904407000c0681c00045031003804803070f107800c0503890360680c1c40c40f284030715108 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 422322158 1250 422320908 422320973
    0x302120f0c0114011a21091e0d0903020f0609030a210903080a05030601030e01050a09051c080105240a0306061e1407060b041a09010906030503070b0919 67
    0x3d031060503903026140e129002e0b8030400a01d0310382c2c1c0003a040c500101400c001c1e6100038803410480e007802644000d010700384103410029520407071030b124006000d5540c0b001c184c0d081d805920008000940e94101c0d1021083d034500c1000803070601803d480c035503060003844c00001c200705c00030005410204c161200030700d036880c10380340650708556036200140002d00100310048440344613400840d40088141400150b90400418907400c5800481d80d04d04103c0c0c0d40d01001e818800b040060186d10210203e40c00d14030200214000e0a915043c840e40d0f018507588540c1c5282050484440410180708440c00c40d115080404003e01404071840386c80007144001c4003a15001005880c07621104005443ea07840509030302c1010126035000040c1039805555400c010b01241d40c03103001e1504512048007800030070004a0b0108106402c060780180302262403c0420000114080162070f260b503000240b82c1100c0c1d9400c22820305100c8990b085101d142140c4400c1c20803c00e1a903c50401e400c4840548001c03001c01ca07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 422323408 1250 422322158 422322191
    0xc2719032d150b01021b01090306050718091a0609100302031305030c0d0e0d0302060609071107090f060f0f03120323090601060e030303010909060b03060703290d0303090302120f0c01 80
    0x51031f4005480030344207001062041e001540c000240d85402215240d80c01c20701141c0000942140320180d03116403542d25480044c421a0101030000c5400d41d00d0003205500003003140c46c00c40d00f848145500440000c0c1000907e9000070009078000003900e0b51406002459601c482c841d0700400c000c1806074a5982c60ba0030710f41c3c1a03010440c0e06800400310303501d8040030030512102c018410000c1003044a0801900c540a0000710018102c941e00801c8111710381324201e003592030540110210310f441d002c0800c07200c24a0003c1608076a08041c00004403004c0030001c401401c0c03984252120849015020810740340d1025141c4c4c030602d41c080c1a034169903258207085030610000c0c1140e650652080c0014002e10300540d0003205038910a80e0002005199500800d04200e011580000030035030306c415446800d01d00c0d04c1441c11240c5402c482e110510034050018490107102c01c00074040558810908003054000c100740e80710016584641c0b40c403001d000040b02d400754000d944148155091a20720350056154 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 422324658 1250 422323408 422323453
    0x2a092a0a0206010b03092a15091302070b01060507020f06030f07020c0303090d02210105180c0103050606030705070c0e01170106121205030c2719032d150b0102 70
    0x10090682c000c10040001d9904249010b203170b52034041a91400019035400d1440070850741c14230032854a071080c140c01c0148202c440e40300c02c0480c0d80100130801c001254864142d040da095410069125400750011401041d042c85403250016400024000c2002d0881003440c8281c24907800c07500d40e2004001496103901540d9001ea13041507820110100500c0c0009110404070344959031100000c1102c880142946c82c15515041185014a1400e07010f4400b44940090900700f801d043c403880c1401400300d410303440024204030400101103220003c2000e00b498030401882e6810024859503140c44101e040d807145507403002503d61070b00d040000c44040c6421100680c3d0b400802d808140b5a0104d42541c195000801c022054601003103060041d5021448050300640c440c840022665403c1e020300c0f0007085403d248441c00c4a81010410000d42caa07410010b284042c1010f1034401070b601008c501e00031010a10080440700c00c07900d18034161741c00e0382c84a140400e090303080b5034051007080e1007506c42982 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 422325908 1250 422324658 422324671
    0x50a060b040605280c0302060a0524211e16030f0515070804020a1e051207081b0a0e0403080606070201171303022a092a0a0206010b03 59
    0x501c401c1020714010b0000e8440300c500510001811a03000884070b20b8800f480c004074000c1242e00b940403081c983e040142690180180804110b80d041005920155010f41205010701e440001495501510340341c510800c1e81c0c480c6418001036070941c60925032100e696800c181850f03c90503120300250000010f460890210440400c0e04660854959500c00180e02400352054070940211304580f4400f0042c09100750b42c3c50740e600725641014410400b406040d680f04981240410140607446e4550b166003208403082240c80c901100310f00035060303003842c585912040d401d004000f110880200c000c0141c0b095240c04542005d1200d8030307800702c0c848220003501c01400007550400090f10074200907005084c1d050050500d00c04c2c100d030b900c2c0c00e560141012151010130150800610b01015010008907458000c5110840d28070841003030b1008043d0500c0e01c0700762280b801c120102e038500702d003001d50081e12030060503480c00c0c00d0401580c8040b1988807140000047c81031070b0002400d81e1951055901650 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 422327158 1250 422325908 422325929
    0x3110609071e0f0b1b03040b0d0b01091d18030a03020414010203030415110405120f0c091905100503070f0e01050f0906060702210a05060108070807290d090204050a06 73
    0x2401e1121900341d03178120452104c0f508400707800c5090300840802c041d000909510140c1a6275178030708900340060305d030411100c5050000202c4140182c0c4d00c0700280702e8007450700d1401c441c0213548410201e400b00301001d1140006000000f07200c4240c551540042065a6060a030904a116224012030f9244401c0b0740190950307400b11300c5000310f400c55800c260504410740310007134105070f19040000e124820b8a041426982e000352800c5450100500054103203004c100d5069005107051040701c0c2201404003945e402081e950000644800280c400c0301025041c054115550140c6075a00303003d1400035805a12500c6009000014492516031a036a85482004c0d00030041521040c050041d95045403404a0780021030000300c079142c6041d02c12580141c0c1d00200244540320031410308504285c0180c22510054002407400d220482d000901881100c2d4035195000ca80c40e205250f2840d9401c03c00c4444c03241c440005100502d45001e0381201c000305d4000c540410207901c848e01c171035044030703560722503a15501c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 422328408 1250 422327158 422327189
    0x21020f06040c121103010204090b041d0309040b0621061206070203040909240b1017060f010215010306050f0601021b0112060e09011406010c1a0403110609071e 70
    0x180d2542540740368003486660b080c40c03607000d04c200007401c0e40c110340c0210303140c542c1d2060300300b88601c0c1c0f900601c90030410b44100d03031a2014507888100c4d1a031260100140c01103031038540d0b0f816242c0f264070840300060345c80d074407041400b40c261000780410107007070b2010303445045c01c0c0034180760003100800d13403d000b1003a0750019880c040c40d058845003d82100700d415034815242011780050344440f941c2d4051009042c210001d01041b030b060030400c84e005d45920060402c44482d2604400e10341140b216504178904482601880d54940300403450a04210100c0c48a600440000420026030b500514010920400a420280e5654004980d100342c00780c2406448000090755440950080103500c102052070b07180820042d032200400010b4840655100941c0e0399901340031403101c918103c1040d0428004d11b0300300c001c0e140170b0302c980450744c00d0104e03800c40d40c80380c28000c101058010031081e81060f132000c058802502d0031484880c1c80d18650b200d840700b01c14000d90701c00840b182d001002d0b1306a40d6115081070390b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 422329658 1250 422328408 422328419
    0x90e012418020403080d06152309040603051009060c0f05030403030c110f0c0f0411030114031504030c03020f0c030a060f2d061d010603020306040921020f06040c 71
    0x2056800c00d81c00c00d00035070810002c0f020401d45001000024104038012500d103240c80005528040b80e0420f800c100315030074400101c844980c0300740c0965040c02c003c005031a51141d60004d130080c5880e50000300719110f0088070074110703000340d0001c1024038001c1c00c081040103141c6800343d41c101000c100180008800300001030010780a03504c040801040d070302d0007410300c010601c28586840074202d0804031a6109014a0350240f41031042803050001c152000c0c0721141d40030028020a002c12b0103103021555030451410859101000b400941c070900741204603c604050030050501b922a540550050203a00300d800481c03000051030400d43e40d0090014401804651034003070040c412100c05c400309513151540c1c0e1075004040080880510501a071201030b400740c95036801c0459402e544440d58a2040c0001d20400c00c1c1190b000390704660285c01c0150b0b40b5566034000030001c1074491b10040c10900607020502c0c13003d0202182100900168080724004044058030f00c1e51040c00711401010000440c006002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 422330908 1250 422329658 422329679
    0x601090e040302010e0d050d0e0f0307021c081b062a07020a0e0705041502070b120a020706050f010f0b070b060f011407051f200f0403020901090e0124 66
    0x1e001d0300078030002844800e4885040c0c00c003442840c584001400100e0308100d000c00303500c01c4a40352aa404010300300419607284c070035260300a411020303100b220008040000108000c03280321500da0b01004041e0f5500100c010394141000c03034040000d41d8810140010282d4440d901e11903a400544991150064010031100d4429440344404a800265007100051003e94900b00c25025001c907481e503035256800d1480c400c8101d0a40030303001c82190702c02ea00400c103903c548800c5850081e080c0070108030317680e25101d507000640302c0c4920051803903203088100705042c001e076418a07040c1ea0782d01c80885440340d40d510030444140a4500c020b0a403000c0080421824941240c1c030f00d4081c081070401480400b0b000400440780d800c100801d840307942107170914144841082c0c0725041d8022400c2001c00000c1144880750005035044058008400400034202d5580606141958000d40e8010142810b543c2c6548558016085401401c500c642c01c0c1200c080c059040c00c04002c80b0100714107800410189004010360 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 422332158 1250 422330908 422330911
    0x80c031c05100e0f01031709030304080604111c0308070e0613090509010c0518030f0f060a11070302030307140d231b0d0c030f020a08060108090601060203040504020c102d050601090e 80
    0x40f21f56104101e1070f22103403010710140005000003000f0301300d140b4007400c0c844007032450035507503c0c4662030a80550840b0103000000c800e0b540c1d01807412403c259030380c00080d20101a40c4034071950100b00400c201d190981660070040640300443d4044c800746d15461042801d8038580c0983c03d0101d14140403285075565600014590761000400f11101a0306901120f0f082c00f1003006010034907000202004017801c03590061024101032600410300d44032258500039100e0001074074000c00c10860219060541c03030f502c025500108c400c1001040b1388040c2d070079200000b20740003001c20f606402e4007001076024280b180443d03500e40c41c0d08000a20b0014256000c078010409800c0d2b140506507185c501d021100c0f194030142a11640544170400d240c1000c60014140501c000e00318141d0b0ba2203c1c00502c0f60543c080195411140240c40140c4c840071a5490b442c2000c0d80d10400031400c0380341c0150041b075000c400c0310454021501031100070880f07070446402c800b656030489145000c600d0103002006003600d03111066 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 422333408 1250 422332158 422332193
    0x705060d020f03010e1b1c0b0f06130e0109110906031f030c030201020609060601021015120c060809011401030209060118030305090310020313080c031c05100e0f0103 73
    0x1442c02c2c40c0c02003885100d400a03088429149502010400c800d0500f0300342d02a22a0091002d905103115443c5100d03104a41822400301152140051034881d140d070700e840b8160a200400d00742d102c480301c080000310710002e403045400b864486000040c1d61210380c03180041e4482c01d00b803130354902041c0100384841d40d4005010410041e030000200710a20640d00607a4000c1c5220307401512103e4a9400021300d009001f80848029400036014010540e80000b0b4417a43d6001d20303100805d0708045410038030018030742030340710348450f0703003c03103080010016450783c040b007a0b07143c0c1e0300c07160100d440b40040c06003201d01052103120261031a03c014409850b100c07000075407203581490440c0074000c1800c0004c0704c03070416500407008520040350070800c92a00340078140d00184145421030440c5001c0440d40c40102c0d00d0040a00300110025804613031603030500c1281c55032100007000d5901519000c050b14010101107541c0203141c1440d50011400c1e40444060780d0007071040e101e10030040d03400c60b140c51011003038044c6232 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 422334658 1250 422333408 422333411
    0x1d030c060703110a061e15140f04020d0605010305100b0a050d0b0d0302010c0f2a060b0a0e0108070f081507090819210f05070804030b09100c0f020705060d 68
    0x100e28003031100b00b010304c01c00c0b803044001056003400f08143d0300c0300030407060720000348a0030806681c00302118242c1d20811243c200b14402690052031010900840b00144083d801900004c0c00c5900e0001030b402000c01c580003079804021603136603102c2d0450181054060810810400c008044425104a004c1c10300162001070000742e95541c2000616030300600d02c1c0803800b603512100903085280d00400340c803181a03c581000c0340000000d4040740b0380d10548002c000804c0c81c902401ca0140501c0f548003801200740600030405590f26028030103040346091041200a20a50102081024103e0829021911000024800d580607c800031101d41d000421400400480040c0003512040802500181c442404030311a004181070800e14004c81c151040d40006424075128508440d07403000301e940b400f508a2030f00c2622040705281c03d403202c6c86103900241002c041d81341804450741c800300300300c2010500c0721420041301403545030a4903182000c24040026070080720040040303040c01802000c005450000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 422335908 1250 422334658 422334677
    0x70b04170307021e0f0a06110d050405100e01021c09020f031014010b0a05090120060f091603171c0606090501090b0705060105040b03010213060206071d030c060703 72
    0x90310200d5801c101c44050059124600c400c09165070f08100900c1004501c0180c9240e0714152001a03580500540c000e1045958003c01c00c4104d8048058601314403800384e003800b060410b82071059940e146100c0326064180780100f42000c80c0414801c442c944040040800204240d00c40c81c0130040044200c1603810002d0b0210566841d81c090240180c0711884d070500203003100d0b800ca5001c3c00e001e416080302c035038000100540f00d02c0b80d13000015948005c40c01d1801e881007900400204d1122100c0482c002e81e00e100d0941441002440200e110344070320000c0c0704a600c8010000c600080040c11884040d1111040b1485a002e161a080c001e001000381c1404d0110400713105550303041124583c2e4021400202c104c1d0092200d503134041c4200000b0420144000c1c00c141c6c0c10f448254465906101d406d1150341c0d14002005940c8081d019250703642c1d40401c0c42d107003050307a454000e52107500481d0355100052283ca4280c14241440c20240e41d901009001000810040011303c00b842e40300c0301d01942405101d20703 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 422337158 1250 422335908 422335943
    0x509120f16150e090402061602190f05010806060d0c2304031505040c29070c0602060c0c1c0905061809011706040605040f050d18090b010503070e0103020903031305031908070b04 78
    0x1c240ae81500c3c096140440c02a103400c0203202e030390040781c20a504004c8858148481d42e500c2c2401d0310b2882001100000b403a4034400002d4440c40740219010404140380300d0b26400400c8114044c0007200e015141c6d002d0205d17138050b8900112542100d00400c05100344109108094440006104d5056403000140b0405031390380300100b0741e8002050850300612a000f082c003011740c0c18400e0036044481a8080d500340303411015801e4440545610004408580c03c4454144900c0b905079100103260181610350358411007504a20580c0c043c45810703019143c00c03000013407880c2e403d09811030080c8040c070180c0a00c0d00c545d61410081c1070007038803d44190b4207505482011503400c1c8a1404056010b45030000445007610060640e10f1413513012041c89450003040c480c081c1d8109003202c2e80480f0030324000d03400500c1301c00147c0c002d0161641a5801d4400440c01c140ea80d0741194002c000e866085084448503208003680304040f140101c1c0c0101003c805206000004200894058005200b0711200e4407448026 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 422338408 1250 422337158 422337169
    0x318050d0303150906140a090c0c030e01020313080c150c0a0305070204020712081806061f0309140f0f0307030212070c05060304060504140d0509120f16150e090402061602 75
    0x190424000c0c072400c2d0f03604001ba4900340040000030f143d408014480c08250900140c00400e24039405018030019a02d0350241c0d070701c2030046070070103a0f4404030011915268156190f4481915003610300544051418141d01c0102205a5020b0300400d4000e012442c2959402c9030aa009900300b01d8029409020107400152208944440d0501684d142c0c012480c040c000e2800b111949060303689990003201c103110341f81e21000d0125030449038040c81c02000c03d060410450080402d2000038045201c01416420013010228131521000c05074012252614403040b14030351244984900240541d001041d2800a000c0080217404035501441c1000f1140303550b0b4020030f050382c0c4103c13002ca4005644600b00030401c000b1026500801000200400101c024240050803070300c01c0784203080c0300780d4185010034200c44040108021000c0310900340d80c00d030001008020b5a1070b0083c09a40b020445000040300d1040c8140070090000714010303d510429165902441010392003007070458902c090001207040540c444 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 422339658 1250 422338408 422338421
    0x1a100f03090f140607030207150207050f01061403150f070c030c0b0901050123011205131709030d050a0f0309020609031b0906060408060a0510030209040309030318050d03031509 78
    0x40c1a1104007480f8043c0d0903410f044000b030800301030500c10b01110300402c807034051004100d17050b58401a03403a500360400600e000c00100c2403441941c204000442c06888007071550b481950290104d0300c08500c1e1041031500345404031070700380c80c03e401c1c600000c800038030503580e100c0d002c1d00034100103042010544a542c07801804a070194a0f5030345072401040301d0100300200c0181003001c2caa118015410100000304011804111601c405031110042a4041c10a001c00c0d000c540e44080d440008203a04c15030360200303400c440e601c039220303000c0c1206511440d4000d2044803038442040d6a0181c4100364040c040e801010351503002c5c0d800c05000c0c040250151030801c012075001201284680b04041000100030742c1090041c155400303480706010030020041d0000d42c01e60130039a80316010400f0740d00c04c1c000295a0403160b102030b40c08889002400149030700a40c0310b806032806555400c6031440f20078840c20a074121482902c1c0c2240000c42c1d0003010a01c240d00041009010b5091070707a0a0343e5500d00101a90751 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 422340908 1250 422339658 422339663
    0x9020913080c031305010816020303040b0703020405030304090b1306080a1403130b0304060b0a0501020a0b151f1715130608061603050105030c0901291801031a100f03090f 75
    0x101306000780b03c0ca40c3c01104481d80310844001c07040440300c0040f4000c0d02c900001d0001071403081c1c00703004030b00c02c14080c1c1c050303501901340981243d448a5640c0b0858014103c4032101c14040d0207109a5841001490300481042c0d41c1e05600410405c1090740c1d5018551035055030246640c00244120032441d0004103c1000400d03600300c11a80328103241c200b40d800c0b900c440b107c8510942800c4010481d698000c600d4503d015000a207140e0f541c0c5d070b260304010700c51154211960784101c130030010010749000840c030000f00d10801e41d03440007803490b990201c103481802544c4040344070040310710400c82807514005c003103590110740c5404165141d60f100c1d81841d003202901c481101c04941107566507403075494031a060040c00110b0080c01514480c10101e514441d041c010140b0320140c0c5007610940c200c03050f036400c46130305141070000da580401c010340c00401d003440044540000c0c281142e41c0c4c162403d07529150f0300501c3c01089050000030b01901070307920000760b54407041415101c04403030f0302050840041007081d50 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 422342158 1250 422340908 422340937
    0x3041106130501180f050f010210020307080118051302100201090605040b1b040f0614191707050903120c0109050703080a09062109151805070909020913080c03 70
    0x181050000b4188040030850104113034002c001c10004144c00702c045900f00d90302624800c2032008074000403801c00310b40b40d100500341070001080c0b00500c3d40c40b081d81412661200c03240c0414106011a044c03c0e1081941c003405046205000f20000d0710f0220b64410000340e4a0000183c401031590741d44050710400c8034166000c2d052440bc01c50980c01500411018010398411145081e00b001080c1031849010300441007007148100f00354035420920700032505500004003080c1070094880340d004121000c3d80402c0c04d03400c07007400301180c44240074006a621448008000d0f05900b08030b52003945298010921b0039040d50340b02c1c015030380411024040310f40998040c640b42903030f032003001e000601240a60b0f4002e0041140514244c00465084010920341c215012000301d200c144e40c0c24040d20004c40c8891444483d80707800e12a100445220b81e02c3c0520510620985d910f0547e500714250032540f81c07032000fa4101441f440010324440b0ba03024000c4a4038070411049051102920441d803658102c19400030030103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 422343408 1250 422342158 422342197
    0x9020a0905090a0905060903130e040515010b0c150106020307020f040204090e0307020a05010801030209040f0305091302070303060b1e03181e070e0c040e190f020d1a0d02010503041106 81
    0x104046c404141c0c000d6007900154582910810111441d5882d8400c1031011020f01c4082003c2100a10410b0f02d03101c400c0f0511503c40d61140e224003856071015080340844c1c4910001883c9010300c51603c54105c1c2c02c2e50300a5801d04c1102d4090006040d6a0b501c0035511690810001c10303c3e0070340c1e100750100c4280c901d00850316044944141b000c044c0068002a040c00700d5500100010ba80712140c00c0d81c4141c1c0130f20500d0040d4941d1400b80c9450080d00c0c1d41c15803100b0640d03880c5e6411617155000d004250b003c1ea8060040c07507600d00d42261103102e900c9003421800345880c012406125290b006640052046130207a924000031340c081401d015031250b00d544001031001403d00d480c6401c20000001d003082c010808014200304881036007a100c3c4e803240d1141d80c44407400058013580d101c803081c442c0110070700040c010702104004010007075000350800b20300d0b0343c40d080c2421328038800ca41000d401040007070089083c0c164103400544850b0401170048130000c0040401c44210f844200103458056003695107200e01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 422344658 1250 422343408 422343413
    0x20d060c051c02090f011d0301050c07062016021c06061701060b18030c0a0801020301180510052214070311120103060e121b010605100909020a0905090a09 68
    0x60030142165403030b410b0062180790340e1545c9007403298003000d0f0242050342110302d0380040c8822401c110b030701c443d43c107505c0d000c100204941c511006200c180d01c00d03081001090034003410366140100c4211510303002c840034403240c42c5803e40e81c52040141800101042c6402d0402030858103102070310a412110a03455010402103207012100320210f803051030009000d0300d03040004441c0d003406542d211030540016250364404a0b01c0c00d00824480d264041e001c500c1954135811441d001c1e6000788030302c441414104480181103185440b601d03006004c3d0303810441443e4a132800b003103007803101e456148803068a8116648030703403403e9102c2e804500c2080103961181d49015500507048804042c8103c5e1b04100030403104048681020415041d41c1d030000d000a803200c2c1c045e80040c644402c050341c664003064006000b00e2102c185110320350301130007104024041c05450b0001e02c9409400320702c00340e02060308210140050b03405600541441d945034074200011541d2140010203401c0300741c1c0c1025020307969500103010b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 422345908 1250 422344658 422344687
    0xf03060b03030304050d0302090a03020d030c030f09180f15080a030f0c080d1e0c0c0501060605090916021f0c0f03060b2d0c060915071704020d060c05 66
    0x8006001ca018504510342511165100c801034020601055400281100d0660320114054060354001c1d1021002c09424130300034010400d06c0f4019800300b954085145040c41c03180c01441c0690300b04034107410201c0c0000c0c41403800f07080c4410f206440303a030b01d40f813983d203500c480084154010100720000303002001c03241c24060480d4203d10711400411a400c20b000c0040f422034000c40e43c242c1da2031100041d03965855401348041241011880d1109400c01041e81c0b915603111000b01c1510340034800801400350742d01e0b81611103104000c6030540284603000000c2c10007030190034844403080240141c6803005c468a450101052a4042d00710368103503501c16003441c2d154007590b04a0244150b003410001c1c0c0e402c01c01400070380d0058003400088080390188a19158420074400000e02e006c050b841900d44201c0540300d0f4550b141100d0300080c80c8206050789a0700c3d003804803000e019217055120b4000d1748007004030b2880384641c020000c0e60409140700c0840c001070f100d480703080d182d50200c2c3c0e0b581d82c403005840c04020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 422347158 1250 422345908 422345921
    0x405100611030f160c08101505040203070e0907021606030903110a020109090c02010b060c07061b020f010827061518060d0222090308060111060c030c0d05010f0306 72
    0x880d803040c0540032091420700101d07440030004c40c030044404a09481c01c1d482d00035454110602d14020640025000f00e00c907000100280d40b06598011804c0e00c0e60180401c0740000c9962000044940d64408000e003040100c0541040980c0706440001c100341c0006e529092880d407141c0c0c000703540c0d0054001450752018051010240100242c098142c035500000c000c0b40d0103004610116aa80020031000d6000354414040000c001d2302182c2c0b00c412907044281c4481083c840c49000c43da500e041e05880c0b1907950703001c00b145a4010030070180c4507249401120140c600034401c40074240c556240c0c4080b250790640c02c800c1c00394400000c1200b4a0302900d980b0300942094405030040d03240309443d51004144220700d90b4481c4040d5507419281059000107101c00e0704050306188000390300c0b603030060002880d07002002141c0c001c0d00c0785110780d2660001102d01d0034040c15007603110381000d00490a104002e130025030704402d2100c1950f0a0881003800c81d0101c2d071003a4844400345c841c1040410030001c145c081d01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 422348408 1250 422347158 422347187
    0x10270b04050405120307052b0608120316170f06012a1709061306031515030f0f06081f090b0f04060915020a08091603020108060d0204051006 62
    0x600c81402c190341d8040e600d84c001800a10010000300001314882d00c19825501e041da074128441c000288104000c50040d01c0901c07030130001a081010100d03041c040060401040c0c240e00c0621391944c1e803400c11303c5002c480c0f41c000300030410001050351450419401c1c031542c01050303182c0b060b0a003400c0110014206154140d0000142800c040050100d001d0040803030120340d401100380c1e0b1008a0342c020741007581c801c400b04070340d00c2940410502c03165000340c1022700c1030f076500c0e4404010f41d0050403070055086c5802e03c1210440061300303809038090b43c0b007600700440d40814000c004c00d81c15280d100720402c0d501a40c110022541c00f0750100b40196140054001040d0b4200b40200510200760311030004c000d01c02401008051a0100424100021a03000d034400d603401c52824034481c10008181c03006944003082c000e000030104404994642d5003c00c9200072105105a0382000902d10390056881d08001806070f58004006402d50025844500901d4400c210750007040000c0360400710007030b0030a43c05000c0d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 422349658 1250 422348408 422348411
    0x11040b0402311208031509010b0a080f01150c050a0b01120c050f010c0308180a06140709080309010e0402041a0c1204030c12260c070b130e10270b04 65
    0x3048482c03824040907008580000e0036580c1d0f0355400001002d40da048070081c0c0e8000d050f000000270f000e00500050034190541c0e9659034100d441e5001040c10260081c02880b0460715510303d0044d6050003403089003c405d115406460780c1c14241d0303c1307038121154240d010000b0025500d4000301000300104158001d0581216482044140000020407031014076000805200000011584403c1c2d00364804190201c40c1d002c0b101c0440c0346181620252905020b1026103c0740f500204006900030741180040d80c90400003141441d0a00c0011125111f4186c403143c3c0060f4200404900608408001074001481070589d55582e040303801c0c580c0c41e01113120450710914105000500001d040982301c40d0480c0c00074450003428401c0c0c0d04040008007072040c07041f1801e10001d01d112502d4140080a00031004e010401d407640c007079490040703510700e100312000f1103882ea24440081c003060100d00c0f021500842005054441c042c0c80315102204c8089076656015000c2181000d0030561006004e846400d0000350790 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 422350908 1250 422349658 422349757
    0xf0e030310090e0a080a0f080f060d06050703091b0509071e20010f0605010e0a0305030d09061e06090617060f0a181a0903031311040b0402 61
    0x1050038030410540103180c101034641c03d804801040c104290035005030000862a601c9035040009407a610b4031203041c1010400001c0050901c0844030f460510940020781011800a401e41d2a000100350040c04e920515640d2409140410900290003004080951001e0f40340f80c213081c10050401c100074502d40400c800d110402007003508402c00c0302000350150500c0f0b40c080403480e8045619000c080700e030386001d41ca010b40765255104560020030844800f0388a14255038030000c18812042200d00000d482035000700304d076081c0100726a200c4d40080d8015140058244ca07090707481c1c44d0744005802c0e081800d41c0c50390341c00d011000c03c5201e04802481031850382c003c8400c5001d0301d580c603010300030044401300490341e00261039000103400c064150300001e07104000380907041c42c040440006029021840408010016000000000480e40115107850350300c000c00ca419920a820240c40040c0075030820f4584840015a8a03607002401d081d007401c4402200c6130800034000c01e100c001728400e520040c1003851 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 422352158 1250 422350908 422350921
    0x3040302030f09010e1e010905040b0325080d020322051018050909071404020405150a020a0c0b0a0e0406030b0106050d06030b010b13090506060306040f0e010f0f0e0303 74
    0xc12614070610b507070000c503220941c070340040c2d520810f104080d6401c0074100540501c00305d0a07075145180a01c09880e2048060749030403c3c40101d40000318804e8140d4481c0f2810b441d9040f43c80c421420190543e810143c500b610b412045d8209025104440701503400400c483c0152040082c0080301d07031020082c2c1d410010b10b00400525411480c031940e41c00d001500804200310800d00940c400030f084e014119901d2805c0c00801c2c65070300c0500303124a0312880c0484014203890b103094000c54040310001441700007410301241520880780e000380184810341c40340800d042c2c0098083c52a250081007401059500c42c51801d03030141c207100c00003800503c81c52400b0f50600014603100f4401d410f5992074070300715072100040b405c414001c215a42000c0d0032078140303500000c0c82d84806e200418401094030b81c003983d036a69801080c825210192111940000288006456410a80d00c680e40e044012840442c02c0d004488829003104c0305050f810110648501c103008000d01207000d48000c0c080118000c0d8603518000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 422353408 1250 422352158 422352163
    0x1106070b071d090f091603080c0d0305091e0a0605130201140a080118020d0204030b0103020f0d030e2b03080906090708060402280b04030614040b070e190308040f090203040302 77
    0x1c00b81d0341300703070440300c08601c00c3d0901b040381c07a01c1032180c0840c1902107502c23410012102e412042040221384201065000054420b0240c01d01510352200100b41048880080a5280240c0740f022005845600c6184c00804c1c45e6026050084a10101c038070030100d940e0000501d20520f491005289520800008041a901410550450304d00c140c085807281c0802702242c000c5c1c4581040e035a8214000728000c0f00380412176104504880c401c85207401100054028171081041180c0082c000c81c5c14450170040e641082045d0554000001c1c1c9000369020480c980e0200c00d61849000f500000d02c0380d4100865140b080020f150402c02e90740040c04441c1c5450b4910f503490034001d00090081000a04040b15201e11072030700e11504043d082801d04960300c0f010041401e81080c4016590a0b0a01050000c0e114001c560103020740e0b04201111a00d556000065601903100e1601a4200c6024802c01c1050031840d24100c1c0914800c40700300b0313512840c08400c1c0d0000c0c0d103d0341015080d84d204105010010b03400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 422354658 1250 422353408 422353411
    0x406080c0a02030702041a130f0c02010e031c15090c030e01061505092b1502030c090d050a020402041211120a030f09080a031e090302011b1106070b071d09 68
    0x1140e001c1200120705002c07085440c0c0011010350000102c1810203291081d58100c0c09c558802044100080b4000724001c900703039030680d0f41c805010b030410403ca801c9852061100052401d5040010410100e001050212490154490340c01d40da615094080340b80d5040c0510191040060001d010040c1027032099034180040034520810700c8000030780d0141907110001920071b8544410310040480348615484a40f5160626007242c0b01e68001c070b0b500525000074403e8900034400301c4c0c2c00d00d081006507824045403001060003940c4500c100c0590b100183d035540001c1000e042210140002c200581c41d02204039140720700d900b480b4030300c141d000141040740001d04421540d050b150025000194210541d4402841c2e08220064000da010f08814160400c541241d021650741a060b036488824104541d17601c002c0c00f000340041c2c6ca0001d2030340d5100b650541000003600030504c0019a00c007110000d0b006070f104602c219200781340e04081104064210b80c01000f00ea407180740040c4004114030000780c03564030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 422355908 1250 422354658 422354663
    0x6051302100507020d050706021606020d08150d0b0a0c030b0402040503060a020f0d0501140a090b0a051509030114010305070b0c060604050a2d0e01020705100902240406080c0a020307 80
    0x100440c1180c01e6544000c034502260ba000002d030b07969180c403810000c0d02d8ae0a19405081c441d0001200010110b1001500d8846004213a40e107050640320f40c10088501c3ca41c5503c00c035885003403440503402050700095014018042060001800024500c024060f1141c0c551130f2440381d0302c144400c1086850102e54581e0281c0f25030001a40e80c0348082c0f040140d40a0722420248441c50030f000803941e9130000b03141004020085071028201da54411504050380e407415001d83d0000240036082029084c0301540d4410340d403140e4000c40c2040305480c00719003165116640070481507006001003040c071600f81f06d4a800780c4144002d15242c500c0c60b010181c0e40342c1014001341d003e15a00c3c0300180210442d984001c011201b444100300b21000328022140000918441540e025894140b809a20311700520855031004c0e480070140c00c10041801c80308000380b0914030240d8014400d4140640182c40842020440741c1c8002c100d103454500700740d8000c0c54000024a000d02c1003900300824903845400105072880d46a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 422357158 1250 422355908 422355917
    0x60405130209280509060402030105100804020102100c020a0c0501051e070203031b0303160f090513020906040f0806060301200309070305030a0504060e0a05010c030f031b08040605130210 82
    0x11160310100d4826a4a4221030302c59004540407410f094102c03104040890702c2c12640f400032030701c4020802040b44420300c10709a014252040c0e100d0303c00c1c051040c440d44140140192412071007030b180d8040c00d031100e2035044001a00001c15000c100034104280c03901038082031074891f007450240d00c0a1135094042c41001600d000340801c18070115a41041143c195454490300d0b07240c203941040140ea640d03042591003005001c00442d03010001da2280c40342c00d11004183d40e0b2040b42a25100a001d01060700e05204032046408014454698444c1401080101000da1054004600c0c001101d81850740c058421032007641030054241401c2c5110400800052041806568a03140c20200d24642201a44000c045002c08100c2c0321256400c01c000d40f0444041d0784410201095410820429400b036005442c0851480805203010074072542c4074082944040c20b0009080c0d400204039202e080c2079109440000345504100010401140901e070b4110b04400c104130211004d0380d002800303240303088080070100b1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 422358408 1250 422357158 422357167
    0x311211b032202181504050c16060207060908040f1a0316021c030f1d1203100806010329131b050901030b01030b160c0201180806070306050a050604051302 68
    0x11402d505030700445070ba000307012904007010300c019045103220441e041c03084603924015048140c181030041900c00c440f8003804601d44503040000c82500c04200c101501d001d45d003032200c8400240c561203000b4141d802020043e44540c40c248c0c01c0000e8003c550024214140e4001c1c0d00546070301c18109490300268220a074030304072118440300324038041103008007034680180c541e00d82e00103603010b91000e2030764246408140652840c2d641c45001041c401171680d1034a90101c40c01542d40d0310043c0103903421a506444216445540780c42c031510b04003083e0816a00c200c44071994580c0e80f00007010101c1550480d6843c4481898910000e40c504004164050290300d40d030b00f1400080c1150380c2c400360142c000184000c0407542c49050031001d5400900044030b0780c01445001c58404492005441125082552001a400c40903801158462024040041070140340d2401240104044c0302841c42001d1580d000511503151404011741c2140503480340d40911001c02c0244003949540b0361032103a8010280d4090f907503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 422359658 1250 422358408 422358451
    0x90607020d021507031e0f06050609131107020918070f061e110a03020f060a110f090d0818040b0901080304090515030109050604110f0d060c0311211b03 67
    0x1624290300f40c10303004046e42102d00c045c1b9000780d000c100d51407104007040050700d4664050100741d208149503940d000c00c0c041500221031040d03801c2110302d000090340b045d00b000743c01d5002c503162140a4a5010900e0302900c2c2540e10380104020703080080440e04840410585000c002619540c8240030010005012042404d00d090103214010001140754040341c0c408411410003d48581300b94000e0003482c01010089101d074500c070f0150390f10840c00c060007a8a84154811150000d0b40020540740d0001040c5001c0004660b00300060140d00383c200c0320044d4035500396010413085503241c05900c0d12805070900180031001c0d00000b41c4040c0e40c2c17910300c00500c64807040380071003004001515496066007013040c0103042050108800380564032071409251035601c5501009011052650140e4004034440340e036030301060030394000d2032161007141000154070804044a1245500150031003c6807540606c001440365115651039a100c0c4d240780038a0900200c03910a5007941c480a4007608843d44440300844c00b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 422360908 1250 422359658 422359661
    0x141017071703090108010f1a07030c0501020d0b120a030e1c020303190f02060108033109020406020c04090b040f1505010e0601080c070203120a180905090607020d02150703 75
    0x2a210040500220716001803003039980794008442180025201000011009103050000c401e486440e500c0b1400009440702c1511103402140d81501003051508000000c40c4007840100814202c00c48046024007070364060010b80c24004a070758000303900941160010aa120380b100e10091822202c000762004400440c0d40c40d0200420040d625000c001b440c00850998110071410041d21500e4099881d00c84003030503a2640000d04c10a242c1d50820800c030482c0c284104000311404500412650100407c401c441000a80030b410500e440c1d9030000d02406866010045910f4181044801b0300c800302d40c603501c40408176409000100605002e01c418001c000946811099080fa501002c101c55030313407541100c05814007070341c03064003107610800030078106a0f18004a44006401500600d11040080c0c0a502c942c2e22412040701001000740807418080380c0854400f0092030080307800f003128249109900c1c1400c102500c3e032030541d4450541e882e0440d0f00428200881c00d500c10b41c00d00b070750340c428405a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 422362158 1250 422360908 422360923
    0x32909060406090e03030a050f04170703030f020307021b03030412060f0605030f06010302090f010e070e0310090c1406130905060f0901060305070e040e0c0f120d0f03141017 76
    0x403c2242018258103e82c003001003e1072142010860a0115403030f0340b140c1c1007050f00300780c9002e4081020390341407a9148d0384030780081200070300c00c0c500002c80034124848401203070010340710803006800c44c8021020300c07605e054103940c58407001c6016600c1c0505d4142114400c40e94014000c0249880d205d8050022006912020003450050213941444000700d40701520780400b4001207114000360300c0840d00321190a558a8142c40ca0520a00003645601400703403880c20818600d580d05104d04038105428041318003649101e0381c41390800708a40c41c100b9400c080064000708a031805600c080c0020031901e22700102400444200380c0e400038864440201140d0b9449161401580208525000080b4607626600c00c0340728226560700c0c5090004104100025a00e400c0c0d542d40f080d50040c40b124009140c040e40712600070380014925100c800c2c64121440c00c0580d03001302503011510401d1011501609030141030041070a43c0b030309500914082500185402440c0248081c9842141c070052a0005c20410707003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 422363408 1250 422362158 422362169
    0x111042c0403170a050402060304112209170c0a0b04060f05010f0e070f05030121060f0209090709030c0b0304111503011a07050c06030702070b0a05040501032909060406 74
    0x140d42440d040c10043d0181c00c095290401c414040c42c00900310202c5440b0f0709008660050040c0c1c5107459644402c0c412407100b0812550003103804001c60b42c0d0040c8180c2490000d0002003012418000c2c5007496407a012003074400140382403080016070709144010440068165100c0a8543e90792280d0420900030119100f16a40480c0381c03c001055915020880004030b44108a00941e940c0e501107007103451221414010340865402c0c401403090312003010103a460030b401140f00c52030740c400c0d40d250351040d28140c20380780701517507800502e055090809881450780401c1c281403c0c0d84140c40d6540d4040844102c0c410904000c01c00706c045020040400c0861800c54001401c4421b40e0215494200c0c0d154000e108041d043d003001042800b00c00601d0056841c01b070303040b8000e010a440110b0610107070394402020a41140585100030600202d500003400800d0700e165151340d2210308100016040720381d0500600d0102070a60b15038615182c0300c0805941e00503003512040343c2c545a99002c1009002c00c0d4000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 422364658 1250 422363408 422363489
    0x30304030b0709152a020f090c0906070f0302010b01090608070302030c0702040e0609240406020c12040314060601110d030903050408070e0a11070b0103140313170f011104 75
    0x510002036031200580c0c4c840c07268440d10381c03031626480e20405c0d05c00c260414000e402070301c0c40010466900e000d82c03106078405600207006161038030714070004002d54041042107500181c40c106460030703d9424480c1030001c40c2e0a00308580403504004010b030410708010042c008254000000554044000d4117075051a43c0c040c0050107a001d03184407942d114002240c4d07001c2e82d40700b5680d000c8500700c00c06c42080d41980c035450300140e60b45c449490300b034083d40c004c8000c80c4041c401c1410540140540f40001d04c01103001d030b89504001c1d807151146500b8650003070007071410071803591021221141c02142d4040380f064175080001700720b1202e1a041c0d42c0381c01250b04c840868010810002500b103904e0b0b854a1045c0a400400c0007161240385004840e40034001c400703040050300200600001c0ca00210302c0718400c05443c2101d061080c11512b105040743c0c00d030851000c80c44040301c02212841c08000c28500c10441c480280103507011034011982c0b82c0558840c45e031301111034840e50800c6000d031026030040e00740807210 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 422365908 1250 422364658 422364689
    0x714070e0f040c0e0702153601180f060e03070804140d020301052406130302090c0d05040c1409160f0309150b030d030c050a0309050102190f0f080402030304030b0709 73
    0xc010b501c03661070620341c55450034410009003c041452500c8c0d240495140c004040c0c0d078000b416540740c0b44002d01c600320104c3d9a6261000380008100c0c0482c40018401e1308500c058019514000083e2840d4a107000d590303900610119000444c507000741c0d0141e80844440c42003060301000000c040c0130001501940552030481445818403030080511880329021800c01600c4010109004403445200101402002400010b00044c60f281035000d800560000b032250509403802003070380884030241c0b404c0b201c1d01000082003200003811684511201c004962504081c548034181c0108030014400b00790401a154291283c61800f86c1d200480341500025848402c525043d40200107014402c7d00d03d129120340011314280910074003c82d480070980c1d03038510b41400080c140940c0604a900c104941c155024407c1080e50116000c0b090200741e21f965504040302411000a030100600c0c1c00c503902081400301c104409070b1000000c0341c08a9511103041c18496484480440342c1145d0781d080300749902c01c91039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 422367158 1250 422365908 422365921
    0x5090a1e1401050111070f06030b030708010615121406011209052a311d01140a0902030715020703390806060d0c15050714070e0f040c0e 60
    0x203aa06043e10001e8889203040c0650071251591041d05100d808254207001c3c10600c4801e2003600080410794000c0c04841c840b40d01c0381e030090b00391142ca800200d4030b50301e42c98504070341c0c2d6480010121000000c0c032081140c2c12001c210784440c000010181410700c480c022000c9203080035175100580040c0c000c0151020022410080210280c600d016400214544041074003145040c900729080c45e2141100300c8180c408668194490000424295000d1a600c150244083c00b041d4407920f84803018500000d01d501482907400d440a0f0060079186626160511110041c1c40015000082c0e40c00b500034010511791940b8128a420040c4c0c20003004007000080307810301d41a008030b00102501200a4500c2c1600c840800f1074803036141c911031142c0946c0240041042401d140d1114170415002c0c00d0307620000c540f0f50203100880d4a6200780f160001d940011160203104001e113009e1607a0341e200c0043c1403032503e00701031070182220241c05150880303104808a010010003c2c0c2100041a042c4102c01d528603042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 422368408 1250 422367158 422367191
    0xf14130e060405011a030412090504091b080d05040302010c02061b1e061005130f050108030d11072402090409060209030105100b030a09140a05030712050405090a1e 72
    0x5841c1d090207030b0706000010901496003203101c80ca50109032803060a540e21a11802e03c0800389441754802d1110b104004a034507100c2d40100c501003401105001c2d00200740c4442c9819900c1c06a0005201da0130404d64201440e50180031102140e4091821400c0003040d400003492510401940444102005044140500022071401c2e0481c00c40d1110111101d079451403561581001c44420540c1c5071807403401d024034585140c2408405500600001350280d00c3c441b1001194400c0c5c00504880e80042200c1c414094140511141ca100f85030205082054945d6007a849420b50b00744030841080b0518004560107503039043c0c526032076004206100240d06420841c000b9401610414080c0d401c0900103403220746408400c80c111221409004c4c616500c481601d0010000c1043c110342e21004050540c0006008200e845001800740c40955a2134041d03281000c0903404409080081c89410b2108000507910858800d500c840400300200f1003400400300110f0802500c0340410f183d51500c40b01d410f41a100307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 422369658 1250 422368408 422368411
    0xd020a03061802090a060f02010b041d2e0908070606090506181510172d0f061302070503130911070b0a090203010e0d02010213060806010f14130e 64
    0x680c2d8030340322104010303428000342c1c4182002e00d60843d9031600104445803043c3e400a00b000140d1000181d000d070501c0c005001e84103111149070b40f0744003103803001c01040c5040c8500702d0305401400040c403024503080b08019050303c00c221a040201e55843c0b0f4003082c4000c03003080722185a80300d0740401446454407189002898280c4041d07010b141500e01482c403982101c000280a074803030200c0e0304805403980d01000b46030f41440100400700704603860003940904011801902440003800011140c4007c000b51840b01011030f0214418044032805020808210038403ca4012500f42c40a010940d50413819130060710540c580280302d4800090000780d4850b4080f2070070162035200c5001c0c4401000002d021120703000d020000781c48468107a004c80c03140380c19a4031185c00c140c4050004280c4001e030a81d058200b8001c00000005070b5000101080e4190490498002410860609904600300a0700081c1789007005003603c0c051113105080f40860200f0030041d14a495a80c0d82d407441001e840341070f000d640d40300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 422370908 1250 422369658 422369669
    0xe04060204060816230f07050703060f06060f080a06030803150f030105280603082215270b1b16031106030411210c0904081801050d020a0306 62
    0x10300b0007103402450340d1580301c1c0040c4069520004c068042a010f080b4200d942c0c05000e084810810001d040b90030304001420787d16010b18040d10032545142040410b9803a41c0314501403484c500001030103a01e40141200034040000c1c9880707002a582d919081004248076007000d40720441c040300300440015590019154080c05480010400100805140c2a50f20503201c0ca610b88a1401c000303002c0b0390218250501903004806c0201c0c28607525220711249920125061a1101202c00d001c410340f010030340b90400800030201401840b9165003002485600358034900c18000d48001203070800303c1402c859104c060300c258000241c0d618104200b40130000b000122480300ca000e440c5007104c1c031108030004035084030340204e018030307048070500d04002055000500403101c960340340e03035602c2d255120300c042101d141020348884070840c200100c88501d00039015140e1885412076008100008501340c064880e0301c80c0920400001c90590340068690f03000710f02c00c200c003035440810300c06101a4150401d408075075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 422372158 1250 422370908 422370917
    0xf050d0213140a0b0f0903010b1f090b160210050c120301080f0303060d030c03020f01050c0304110f011728050708100b07030503060f120619020a09120c0e0406020406 73
    0xb0030781024000301c041c841c402c00540c51340500c806203401e45030700b0040907848801800080c6140d0000000394011840b40d032800d100881c54040c00c000e00c2e0308200344c0c001910541c000030f810160b80350403019861007000b40c000c1c021701c0400250f540c4a401070701500c5045c0000010345100700500d1001e00300b280c00900c0341038441d02c2003a03006196800c0100c1101e010340c4010b04503505885940d2015034034040751344003c904500c11000d2000462400384a00c3d4010202c801700d19a0760704050400d001040740304444903208014030b950f40b421a80e00540020380d600c50041003450b07203170f5501c0c00040080200c9000700303051617840d2901d060304860315805a07101e15800e803940d4441d52240704004407038402d00c0c06100f20210f801c024103400700340140d019681c001c0740180000900192000031503c242e1722a0b0308108c4980c170081c18804454001000b500540420590031414141c0b500c00c000c15440851040040c4640d9000c91039040c070441c2a11a4083d00041c0d580c0c04403170a0a24100700254842d10a02d00042c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 422373408 1250 422372158 422372189
    0x9140c010507021f1808030408070e010506030f0415111207030612061116080d0b01081515191d01050a0c1509060f06030201080a0204080d0f050d0213 66
    0x56028000b6a82030703e4001d4800c02c0c0000c0513201000004040c15001003e00924040d000310007082811164044c000c0b010217140c8440c503280e181440c20603150002c80c0c245940d0310060016895000030703640e0100103541040c10a495605010401030101543c40e1900760402e201e402c1e292000c3c00060018440c201c81070f46e50390751103850850031903566010b0060011159401038002c20000c1c0c06c40c42406540006c56440d04c5806020007071104041203040f142a034010503203808006042c8941501d0b01d001b070030501e00501c0e017402c00e0103240504440d0b4034440d0800403290300100065030246c42050701e4031400c0607200c422031003000d841144008030f0000000c606480c0201c0e1548542c040d00c2c001e007019150000c138250316503254500a4280c903508842140c0c1d41c400e500205015006080540e0301803200001e0241c21400014540b0700c0c01080501e000b4010402008800ca0014107407110300680e2408241d19100040c045500307105203401440124000700301044201e03082c040e18400c41c1d02d001940da002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 422374658 1250 422373408 422373433
    0x70c0806070e0d030504050a12020108090c0a051309170304020a15020606060306182712070803100e010806062e031d0304080d0201180c051003090203010914 69
    0x10345504584020009110348200200c6007414412a103445201707003403460601d6103c4022400b0343d8102d501203120942030b45416000d558025420580050001028203128440c0001162200c58680710310350044040c41084640144c859001002c4a54003480301004400e94140c115225041602c080e0b20030040c0e0744000490000e50710206915042640192800d82d860b04100b11140e0402404d03203411007140f59074480a1761492807000c0c4207440524a0b2501c89038a80e082086505904c651041e1a601c150100c1650b4950002614010341e48500ea096a1390b481c031982124401003607001e19a00d0f4110000030407840c2011503039503c44c10302a103e01088180030100c0740d41020840701030f000c401d510700340c541540e04d200e50032081c601c003a038181c0e0500358409100c03003e01d568800ea104004030341100703280e00e803029428083c0300080807030005403511180007034603034042011161096502c160300315910f01c1100ca000381c11601c80990014000c1100c40f0883c100300d00c85036081c003180361941c00b0340401e4011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 422375908 1250 422374658 422374663
    0x40501021e0601030b0c1603030c08070e061b010209030a1202010c0c03050904050a0e0d03090204110307051801120e010b0f06040f060804152c0114060904060f02040803070c08 77
    0x14060401c401003181d40d2841c1c03211101000050115014003c0801640607101c22042016643d00c1c0f0a07a03002a543c7d01120000b01680d60241c148006c00070404c0e012000d5680c0c401c1a10052801d801e0084180000680380500900c6501001e03505402485018014002d000301813100c0100281c000f840314515000d07040700c41c0300c1c07010002000701d00103014800306410a540101c1e445500454000f820003000f050035031410895114000009460b107000b08210b0a0501489400d041820902410341c140000040e20500400e285406103c40e0380304982d41d030781e108420200310600b41d9071080018000c0b035221396000c0d12186100c07038010207142400003440c3c20316008950403a0000c60810300d070142004d100700d45503240500309070741c80420000310782da4a0607a4421b003121800d0130f5080c01400710201c0072130301c10101d0000b104140f60345031107507401c0c14560304002c0b2136110500f180c045004d551149006401000d80014102d1041d101103408522a6000001007010728055040000c0c800c0c2e607034030400d0703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 422377158 1250 422375908 422375953
    0xd02061f050d030f020a1509150513020d2604031a07140d020915030106090905040302100e1501030803010612020f0409020a05120702060103031b0b0414120c0304050102 74
    0x25006140e04500c82d002c01d1240702464850483c0384107840700c144071a1039981c030b1101d40030a40595203580f24480340c104049113048840074950003000f8030041c5818541402e000340c242c14042c1c0511018180703c810051390010740c40c2508034400f4844808200801d030b000054119020460300d031100d0414220842c425050514460216075440803c00c210708858a200c2ea0001c07602584007680070b120154040c0e46295480300f0b50460045200d40f00c1d031410320000d00e8248584d01203084a86000c0030300010a41c0410b00c812107849410b404969044c0b0708046614104c1c4001414218242460000c0204500040210304035416a61a109210f100c1e0a05070224801c00700701003a0b604080100300002d10f1030b40c0140c44004206d040c12401c0c2030081c0302d1030b00d06034411540c01d0016000b64006008158103c00c000e10002c81c1030b0841010b03002240d42c2d4041c80f0001800140c0350000d9100041c1451404018020074454204440c94031a100c0385181e1b80d0b260445e0044501500500c0c8001070141aa01c00d042d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 422378408 1250 422377158 422377169
    0x105030613050a0b070503101202090a1a040f150e1519030b0702010b010e0111070e0a0902101707030b1008060622051c080d0905191a15150315030d02061f 68
    0x1040c2036107335203070100001c2a02d030114840510003590703420081d94a07071140b00d0111034829404035482c1072480504515010355007201d0000c00c00399060200d06d05d900c046402151006880807141d054109401100104842d4002031050075010108065164107400c024940403080e2074405030b24456000540c1c100760310b054110a16400203000308603403566640410b404c582100ca000500c4002c82c0c02203200340b410140200040388402843c0c40c00441c40b0f11150b07902405d5803800304203400400c0d00142514072541151800c0100550125040790f0303c1a080b00c0d030040c6901048042022101650805000035109151003607000480324035050490703104074a042d0360700648891502d107a40c02844001c001e6544162070310300c1403000140d80068060750507440e20340102101c9104650901c000b89402c40000c7c0040c4d8a840c1107010004152500c0c0308039070132044105c030002e4a950351006041d000030300282d00950b05200b281415004650042075450003800803120445078a40c000b600c1d4000c0d2040352080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 422379658 1250 422378408 422378419
    0xc050313061503170307090b070c0b0306040b090a0c09080d200304030b0f090d1103160f0b1005011103040f060f03021b10060e0105030613050a0b070503101202 70
    0xa040024002d50106003224804000301c0b0700c55441e511606203845075040c40381d001940000c180180c2c2a00428140700034504001c620303103811b149540d0082c0080303140c03003049101c0002201040c02039580f500100300007500078001070500e141041c20080075041b12081ca4010a000d00707004140a0004030b02c4d01107001c0036858103800c1c0b0414490042c03003200d45059000103030005100100010f4034403680c042c0100c0c1d2000d101d841038109000010b00304220400040c3c207020040c100c1002c3c1035404415038a81c80c6407140c07071050844c0182400d05e01c540030084014aa5100c800c100302241c1400d400301c20a0300d90070b9075051070388901300801c1556031042d4010030b0000403614070100500c504c40e1403000d880a0340e5280150921002200d480e1007880d021f8800d0a0070b4008010f80d05070340130383c0c3c401d0000030700e003c096101840d49010007003622108098503180720b043d07c1d140840140107040000324481c5501c86034121441c902140000c10542040c0e0700040304546024002442902413152906078540040c003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 422380908 1250 422379658 422379691
    0xb040c0305010b1911060702100c02060907031515181d070902030a0b1914010c080316020f0a0c0e01150f0f02160810050702010c0801060e0409061e0c0503 68
    0x110b0080c081c0100304e165040100601488080d00003d0100c0c42c002e9841da001080e2291048001c0750171348103000000307070840d1b2103d42081010080003030100100ca4216000c000b8440344081c150000d014502d85800c4101e4801c800050404188200d04d801001198401c00c14030b61841d00c04010303404820b101401c60741c4010401d0003a0352040d4002c40c0c001c1d0f0000c100141e4562500d002c184011260700100440003c144010041071400c48130b4100070410900e0a03000038889541c61007c1c1c2c2c08007620440305811620301c400600c80c0208140321400c81c1c4082240c1620701c0c0c80c45c141d034040880d405228182c4410900024400e8104400104c5240558503501108000c1c0c04040f06c4903408284e9650031846804055600c120071940c2e804007400d004800341400450341803c40056400260205085a00d8695000d00c40e652004030b017419940d091a0500c2032909020010340502040d41001e401e40e441d0405202c62a0903503100f095100d60015414060242c41003002d030f07134a0204581c0079060501c00703017 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 422382158 1250 422380908 422380927
    0x3070605070f14030606090d050309090f0c041403160f090f150e060d0204050a060305060c0c15040606030b1312090303020c13060f0b0a020708061003030f02010e010905010b040c0305010b 82
    0xc084d60748050041c0c506030401c0c1003c00064048803031800103542c0ca400010300604507040941c0f4440d030180303040c0070221041c142605103840781c1c4520b10901480b80b400e120051030075a010b00019805204901d040c102141e03c0b040900c10342d000070300c2901301c0c0b82e103040c40348035201c1d5a50084510350110100412680da1502c070508891050041045030320444d100b840c240180d482d03200c1c1e9405440035083c00038910f81140f42442c0750202c040c050040d0340c203092206107410302c4c0c001000d01180f052010480f20a44480c83c3c101c002c0d01150300300400d060484070800501d50004850141418000e035070440440081440589003030450340009801a00803920000c41802c0c1852244c4450b0010780000842c1c950f06ea004480e904010740088144600020350510720646c1080708802070320070000500140d0402890385094506944001418040c00c4140107403c28000e5100803562400c804c000d0110308042e20300903008018900c02c1034405e1340741c00105440c880c407a106050503203440c0807100303161010b0003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 422383408 1250 422382158 422382197
    0x80106030b010e0307080f0c090118110d020c0a11010c051510032103050c0406050403030e04140f01030b010b0a120e030f0f0d0f09050d270803070605070f 68
    0x2007911a0512003015107000158508012120017003803410003404049012103290b900302000724120301e1280a000006209204401807000409200c40b400042c85141000140c2c40b2802005503030b4403a41e1002c5100351007004082400d602a0f84104404040d0480078401900c1681c041030780a0116070004c4000299803503500d203029040070540301c03160380070341d0b981c7e440b026049140b43c0c0f41a11a42c48403aa1b00c45680c2500a081c4c10100d29070b516800c2a0900b030000f480342c0224440642042210225246261166408607000a120320850040391802140000c6070340d00a1000702c4003081c03840000a00307400040d0680c1c41c441c90302d545640150340c889000700c2c05070440a14086090200f084184102c840c000c0040c015441c80149940e00d0384050006982100d80e102c404250040c2442c8480d0001140410140401c003442d0402d942098400041c00d002c0d01c2444c6c445400e0702481100101c2c1042c8000302a100e0144100421b001e19620107100f2140c41c0c10341424400456803843e0300c0e920a0048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 422384658 1250 422383408 422383421
    0x609091b061903021e040305192108061003051012171204050709020a121a031f0b030f03120705090a0b071e11100c0501020c070f080d08010603 63
    0x104040c1c209030203030241241003246002c0101c08698006101c02d030707441481c0303075222003803a601ca003a904051031611201d488082c19038a50003150822180c1508100000385103801d11041e800d404101e48a9820001d0003030881a180310b44070780c83c02100d19620134031074060244507040f030b003002d10742d142e1503c00840e5403500f80d0202201c02d46448600a9803454141000c0c040241d4404070060741030415042860500101e504039040f0030740104480229590029075000c4041094140001e2170711118030100509075010a105a050045401c00e1219403a685840c444070134902008000300c081c0041055550240d4030648030444d042030010600311016042035a50001407410714500d08800180040c45081c06c5401c0700002180100d00360040c40780c003041b0390501d00c40b103800c2800c420a0603114600b8420701d60800f18030074a022aa44407210380314007140d07802da070341c440c3c029910381010004440e00e82c0900d0056111726200306400141040b000240680c140c88551917031072031f036402c000c0c04038098840c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 422385908 1250 422384658 422384713
    0x9050705150c0f071d2701020d1e0f090209060409021c030c1a07200a05060a050a0b090c0313020d0b070f02010b01050a1202030a180b070206060909 65
    0x1024442d841e01c0340d8040c00000c4401c034295002e01285418101410581d0700c0400e44400142d804104010101140f50f641400ca00d003010000300604902840c01c9000e446109101041181450f80c4078844080d044840b61125240c48014000d4450703682c8030328201d4a2441001e544039445c10045545414680c0c4501c01e001d00181035100d4032241e04c80302c03080d03402000c42e04800081d00d83c8415018405018819950a40b9180320b10180e41864600240f0380260307400c03030b644120242c81c90300a80c3c00c020403001c80d00e1076002064410345d10b42400315034010403040380c40003000c60410b620500145050300049203d081012000f50660301d60341007040d05022240c000320713008040341c070809001c5040c104445124140c41e40d103407074038079240800090968034901b0445050040a00c030300d5021542126540746001041403005072a0380c1c0d80b41c0342c140600102c00751901f0b40703034000f9982c005011445000c81c0c070420998003203802e20b86550701880450b120440d0400104d0700b002c42880b18001c0b10780ea01098154 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 422387158 1250 422385908 422385949
    0x6011d040203100e0103050a030f0503010e27070602010204030c0602060601080103261804060609140d05070f170d0905090c0d0e03130e011205030f4909050705 70
    0x6485502143c101c541c203800907031f00c48d403101c81038504141e80140c0103084a2100e113011421945400e02d83c1000e40809414001902c10942c54a502c00e00e002400d40b500c6210300d4111401542e41d021301900035401404161114a1401c5003c1409400066414017940041e50364041d984c2c81c5440f40d0000e0391100140913000103044211007003420780d050184c010b540d0b001c845105d4554030503040101300c0d02c250380000c2c18000d42d07130000c02200000072441c07003441d007007940d80c08000c44c240d00d86141805a1500404420f0500c40c5c0302149403d114540445000c5501003103516104900200f41c940c06441d1150642c071000741c40014401184150150005000480001c1840c0c08010952410b5402500d0f245440001c840010060b140e40311000e28014a07406210440390805500c40b50344a205262030703007901d40000a803041c0303050703400c20f42115244900c107121403c0391405043c0302c080c0740801c85000d921b440d52075080c6004143d1b5201d00fa942c250300030014801c1d40d1030403051020305100070510b0948407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 422388408 1250 422387158 422387191
    0x1090330020703050405090603010b1c020d1416090e071412070b0310090203040206070305090a08030f0a080c090d02040b0a17010b0a08120423180f06011d040203 71
    0x2640540050101280309488407900c1701c0c01c010510104110081413284660304045810481e030301c501c0c410011402030001030701c1c0d100b501400403a2001340780d9040144003145080c494030040c00003041c00e00302d0541e2032008000701e903510009101911480480c500301a0449401004032085446895800401c0940650302950403421002c0c10302c001c40e803007000806400000c0048a4010450794409095007a004604505068002c212907005840c0c0c02014400300040051003580c07051700340c9005182c6242140da5404003039007506455048015142d000c199800040b0780c00440305000e6032803102d000303001c1082c1400107800300300141107003020076900f1030800307900400c5100c400c052034075003407180782c4c008190664101c0a200c02080698042c002d03c0e040fa0b4803460100b15560120350480300745440450084101c008180c02010a48002581c00300811840c0388664000022403440f501840a0301092075807000c006580c41c50f455034041400311000a0900300c1d61400b5409150400e002100c0389076030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 422389658 1250 422388408 422388497
    0x11090601030f02030703050105031c0909050a06080601180506120d120b03030a030204080c10120510050d030806010816020304270606020304090515060f07020d080a1709010903 77
    0x3c80e4420750340350700002c3e241e1005101c0c5050810241c00301a142100784150b0340101c3c04020060b800c00e003d020103441d00d40303012600a945541008010340400c405560803941c0d02e901108111810003c82040d0760304002c001504c902d410320201d800894000040c0810805689040711161264030100c0c01444c2d841b4250b040c60b40700ac001820004140341c4006a6943c00d0003030441c60030042a00d414444c505030b401d08202a5445001d050981100324000720311511013682d94155984960002030300301a005d41381400707050f0300c5100c084c0900c60a0300d51104540b00c003280201403c04c400a1100564000c00040069040c0c62044000750800e813004030007280c0048100703405507080c03a480b03600142d00100c0e00340643c0429100b034a40003078048102e10800308603440418001c0c02003189610f4200c1021030b0b1f02040d034866220400060381d01003a1550b403180140c001418501c1e00515902c0c41e629a54002120307413005104030400141c050b00c56240c21501d03091f10101c00c078144400e041d0241148101d224a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 422390908 1250 422389658 422389661
    0x601050a180e09070503120f0a0c03050d0906060509090a2f120102041809120e0d171306021b0d021903060b040b0103151a040807090603060509060411090601030f 71
    0x441e203e030082e005407131801c4101031034150000d1591071407000400150704c041d5000b1084801450450820303c510040c1e81c02d040c0c4890080348000030781c42e8108500f90341005810f1303000d201034034001c80340c098803511180e00c1249d07580d6041500030306c0e0207480f40040000d840042202c1410025814210346401e80240125040c002000410403c030303900850203005151481201c40d040c01d038840c40401841410f41c40380c20448014104550034070002c1e1801d00460b85411202050141d006140e6030340740e010b84107646031719070302c0840c200d10020381c2960301007565032010560041f100110b091000400950200300400c01551b420120303401400721040000600c24141e0035002580111030000d511b6070340c40203010581e1102e01e9102d042514040284800c00c0300e005c0c40b50290740d0701c06001c03100c0c0303403080d030700c2482d984100e800c0351803580728660700002d0901d0103400420a89202d08000d11064a8500c1141c3c5d842032300740c0340100361785844c4046000d2030401403031480d0710410500d07000c60300080542d80741e0f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 422392158 1250 422390908 422390911
    0x30a06020c0a111005030115050d15080601080d0806060d02040503060405060108060f0405100b06040902040f0515040b1206010c0c06030b0f01050a21020f0c1f02030601050a180e 78
    0x48160081c0d100c40c02400041c0c1040c00c005481074544044c2c0b83c0300c0c46001440e61105007d2603144003501b10107131001c0381c4102c003038843c001d28100f01040449003503424140d14440034898214075101d06400030589940100da0700c411411a0344886100ea1a84810400c0d9030b00000340003513a0650900000030565420000c04c0c2c045c07070007400904495410944c800f428032900800040400c01d19506201c00107900052401d20a64181c00009403c1d00f440d0005106120303641c01100482c0c00440c020954051054040084648c02c83c0d080c2d0724844c1c1a4040081c40c0500d108a0411003018000c802003c1d160700b0101c0d600680524201644030b001c2e41d0b82c0600fa000c41d40101c000640d640305007030640d00b00888201c80218090900500b40440780780010a00074081076810091015400303d200031000d10b806440c041c034441d032442c54451540c202000d60728120030f007805c2c0c401a44c0c0064a82200c8452003102d0140c08103a40300c40c40c2074050041601c00781c3d080d07990b03440d842403170280c0014003580c0001c419 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 422393408 1250 422392158 422392177
    0x330307091107080a09170d12021605031b071505040b07050123010303080708090d0e060c0109030819140109022505030408010b06130302090601090807060306150201090b15030a0602 79
    0x9801c5d4504204104885c0844c0100409503548803d04840300f89401c124088500ca102c58400b42c1c0e42d6102140c0810603040200e401407007840701180e0307807074042400b0103507004031a481c1c02280d461607626110780807219902d5030450042107042105010030a46a0001d203050350041d4004034161000c0c460820782d440c2201c0d2101054200380c40180304060340450396035000f00b450b01d400c182c03038104032901340d8a9000002c2280c0520108030800c1c541d5403500e9003640e807003c52180017000402a6403d010b01515400c131003034900b8020343d0058640550441c0b0480354000511880381d007141e801c00d10188000e500003150322700e8141c103075030301c5d9000410700d81400314680e4421030141d500c4906e00b600e80750030744440072142d40c418002800014000c1f03104540d500f0440703404031022009a21403c006075034040450300001c02c10f00074104003103402501500107401f2900c0c4440c01601e03001c1944800c900325400c010006000400341c0d0b0200340c01c0b641006510000843c0182507507001340c560b86c0d44404903441000300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 422394658 1250 422393408 422393417
    0x910110f0a02040b09151201060314030705010b0303070b0408130918020901050f0d02040c051312110904050d0f02010b0d06060504050f0c12090102070b330307091107080a 75
    0x2181c045083c1400303001181c4405030740e44025420880d260b04003020075152018041c440307450f0b0706040e8000075005403000310381040340003012b402c1924480d612070340040b0301a68258201203c907906410000100c0d000190401c40b00c00040c2c586a403510300950203a0140c0c1c800540905021030001510705c107c0402c00c0e0980071000c4009200d1050000362a4140d101c984541410781e00c0420f503464805582000d507604840c0021503008442003600e4601170200c014021100320b6401044a1007091402c400c40b5000d07101204014000204101202004541c01040d40d0044800101210f014488411503076076140004504003400c003004c95a1198120700903940c4580f10070040040b414980306081c1c10103c448002015450a100c10308800d100320803550172202420000107903070100c00c0d03064581895201c8001082801d0982e460356001da10310500001d500c507505000e41c90f0244502501c40500c1c005005032610910300504103004251020351150040b03408c004050008038128000c000c4600551034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 422395908 1250 422394658 422394673
    0xe01090903032f07020a0e0903043b101802040632030c04050d030816091401110f06250503040b0c0306030c1002031c0902060910110f 59
    0x81c010251001c98001d00c600303122011101c20315440b001001400c0b600d034100c07076694480340c620204004444951189034a60451020301035004408001001241e6404040c41a091603103111805114018401c900d01060f400c0c501207444003005250f182e122141000000345a643c50600d0241c448000c07240070265940081c1c20300c09aa003090f80542a26a0420022145100001c6070b8584891550310820002c0b00800051a40410017040b103002d4540070380b5103103040b0f649181c081e00360003099820b54650718240f951707240140e22845913034044980c200b03020300e0b50007902c50043d6041c401e114000c0506000e1489200078028003005410b006500c104148819210b01410311503601c8410080d1340e040003010020321010175928454203030070032107101a80b03a4035111000020701c0d00b003061070358642115980c01140340c2703030f900800030b450b502003800100c054880040c03502c68115008050000d501150074005084107051815160880100074288030041000c1051800d1801d900e1842802e1161702090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 422397158 1250 422395908 422395913
    0x90309080706090506032a0a020d03141303050a03020f220b0711040f020c101415150304020d0203061315141807120b04050610080d11070e010909 64
    0x1c852401080c007031416840150400700050140e10001e402420500d48105050206040800c4e801f43c100e1180d2901c1c643c0d50080c40c80180d02c0741c00b010103d0021034035042c40780c0c2c03210b20b55030000d500c541e0100c04410040d52550360290340540201e01c1d400c04059013880020324811456005140b681408801c0540684000c01030f40c4072140e5640102c2c101690a02c56a4000340c8851200c07103240004032804664520b08401d203c0c000d0151001d031151034030a544168280389090760044407a820442d0100d0001ea940c00d1146403119a81e001807034201c045800300c0015010303110041e40c1c0040c4024259900b840740c40e00004c4c6030206c250f444210340000001c0d040e04008100302c941d10303030400b005810310003210458401403460b60010400c011100d4848458801040140b00c07000240c41d458403680c40001c1c003030034640301100c021101140c2c103100300d9020804001d03205403a4001c84140c0002044524020078089413002d1080c1e03007022940c4201040821138403140034100f8013804d418440090362080c0b50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 422398408 1250 422397158 422397163
    0x12010b0306060103290f061b010c140901142b0e06010e0727080a060608060c071b03121205060d080a0c0507090507050a083301110109030908 62
    0x15242d541414940060003a00c910640340d103090b0410350a243c0b015500c100c1c404030b1800d41c4d00d150341a82c404400541c1c581682e60700c40071109a4400c1c00000c02071509101415202c81040c0b03a0300d454a00030620802e001d66203e01f00c45001e00c1708170015181461284200341c6441010b592205401903005240400ca01041e44962500400c21130001d107202d524002c402010184007600d5013003080760810b006d000001c682d54090415100380000b0110030380d0380d03491040e20b604042c035044812a04044000551440000e4114000e0801000fa180351064035914607004038071200c21125010300054001000c00c41d090082c3c00d0320380e620340b10b542d050200c905120040381c40003800148603501d0001c10b500440c400100b51140f180050402d4141180366003017452606034960702c1106403900302420441510f62040240c92901043c0e183c0ca01d89131100760b98280768507a0180a600d12802d2002c003c6d881c101b020114030344480c0103050a051b0102801e1340070b820340b092500b05502042070480e0802c00000304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 422399658 1250 422398408 422398411
    0x1090203101401060305060d1401060501231210091103180a0f29090307020307081209010302090f061605070f0501020a06090501140a0c030c050703050a120b12010b0306 74
    0x6407a0100441911201c40480308907044c0210001c0640d9800021300c0b540f10000d002c8442500921405184a030503403c40d0702030700303590184c2400075105483c070244c00d94403003542461019103520141d08050583e04a00c81080300203003000070051500c0030000320110309128604000510180c841c0c0d50749041103100d02080a101c0c46038031a90310800c00038000c200c1101c05400c0d02da900003841550144000741803840604140c2403640700d0b1400c0300a006441c03e0010051087c24030903419148590368030b54000e0740300c070310801030b451075420104955016903201c1d80c0101048440100b20b9104403041101294a40c0c01202803504c07641099513000c0306001041200d040200301d01c1c07800741049418000000d484a000c480b00a0040342c0f110010000c000c002e400400c04900d0103020b510180c40d28901c220003511109032200c01003072030f25000450361031051049403d001c0d010f8860724039043e2055412600f0590183c03d4100c01540c5030812149030352400488007124100c0c0001080644c500c80816003001d40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 422400908 1250 422399658 422399683
    0x71b031208010f1a1e0408030f0408060f0601091203020102040b040801050a0605060a020a060905010e03070b04060c0c020a0e090c0402030a020d051006211b0305010303030e060402130209010e0a030501090203 91
    0x1303a560040400e224107100b101d01003a1200c440c41d10200c40e89609036030600440e0000c5001c0d0101084c40f81d158648000600200e0301144c0c2142d00c2d94643c0d00707900b100b02c035056800600041d4001c8050191011008035150b01c94400d1000528255680d0b009525540150b0080001a51200b00340420b0094a010f6140540310848003039190019804029650311200c3e080148855140c1000b2402d10a0039849289540310400a40355036034442d10b404030b031210341114200c0f691898040c400740718074460b49080304600d17405032090f6051400c040c0801601c1100814511951103502070490803038459002a5000c0e07510b000001d604c0303c4085d0410300c10380c2c100074018181d503280c40c83c0400405038807031488401186108072809a115032444808050800a442d4010700c80141544500341c5505620542c12640242d80801128a101410603191034040d1006540561116400780860120340c1c01440000d105041c04d01c04003100d507001c9000d00070345900544641e55524110802e5080600ca00d100840 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 422402158 1250 422400908 422400929
    0x130e090601230a0b0327010c05090d140115050406060503090c0126250e0112020d0b0d1b0501020d02071814090604110f0105071b031208010f 62
    0x604007410380300c001c480b5011140d540c06011160700800c0d00d4503a00b40d07015001c0200c00c030341da0346405584407400043d20b4003410f104540301c0ca01310f607145206200b9030201030507603503d042c90480c040040000e0b000749031905540088421704a2001c2070000d21905685002c401c5928694910306000c1004480c0d0581c80b00003404803c10420602440114602502403000d0903c101c5130b40081104021100c0c1190040400078641c8080c807920840d401d0007005412101480c00403200e208010032100c146940c8182800300f10704031401600000750b071b000342080c11070441e0002001e040e0a000070750b140d0340007c000e80b240c250039011201d264000c01e203604040c041c02e0005118405020000130b5444150340314421a0001c5280a00d039410555040108190200b0280b03000724102040056151001030f20100e88581d0000740800713160402d200700b50110380c416183c240c05e00c400b60701d40d4080c2e00b94008900244c1c501500c40440003544c0e0364158240c62805548104080d03050507511580085076420610061 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 422403408 1250 422402158 422402161
    0x11b052803081b041a030604060f0b0702151306030e100e07030f05030409091208100f0512010f09120801060206060a0303030c0c05102c0601051c0602130e0906 70
    0xb9000403109401c44021002000540b07070041403207034540919006070312469000c540a154040107040518000c140c01c0740c080000b541d583c55003406191882c403505008040c240050700c05407508100110f074040e00095410700d000c016104011030711a1503001080400e907140e0000031501030821000c015800c0d10079007000502d0034804465980c911364840180b400c1d00001d94002001000d00c04ea800405040c00240010590340c541403400c41c1d03012038600c0008071900001691110b05214071030886200c0044110294204824031844041d8103281e400d5640d00c483c1c00c41e080e82014411000c4480c0210700c90f08401181ca80b00808540041c0d10000c2158482400d200466507100c8866007100d03418200042e80320000d8006842c0c074107002c5005482801900ea070803c046c03420b508010110145480c0b200908200000c0c2c5001070004440400c447d03600c03510050003242080d01004c81c2482040300b4000c41803c40380e840760300340e03880040b03194914005c1a10801080d0299040542c01c03100e80030152681d07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 422404658 1250 422403408 422403413
    0x240b0909150901060801090c0504140f010b0903030c0d110d0e061b1c12061703040b070c09050c09040c0305090d081801020403050d090f1d0402011b0528 67
    0xa41e24030030841a00c8103070030070120707500c40000d41c031901c0200400070081c40b404640e4200b0b000703260350501c10340e07001e0350920117045a040c0f0000309282c441c82c43c4082d040002e1342000304060307250b04840051a00740c4001c01c14a0b01d508010840d18406915030381d04d21901c003840390030322403c00c080080c8a000f8001881e04001c456603034241554000301404010001030300c121420035141c540100e41c41400c0307a0790045000d101607070164480c40c0003039130300e0418442c0e19036903022846403509028210031550402d103c00d02503a240c2d07038002c21409000c1d882c140d000704c1d01c41e08840200c41c0162030a01c0d201c40f00207545412405c0078055112440701030700341003040385001da42050722251304c00038420400c25206d00040004c140c61100445800b450720007151110307100d00e0aa0360f00c90881e0038001c086126094001001e46014004000340c50320044560000c000444048034003001c0a0003c905206103100c2a14848003641c4a02c2d40e010702440090504080340c00c603c560700c91504500075410160349055001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 422405908 1250 422404658 422404663
    0x41703070203181f110106150c02131103090f06070302070b060405060420030a110915030a020d0207050a02010e0103061a07050a05012a030203160e040603240b0909 72
    0x1000018691146429031800000071403411080a40c24008400207180fa1201307540003440019201564000b0000203454181105d00c3e5241810301c1e400240051103940018184201c440b40280d1010704040b46111000d000413805401c12910090603602517070800448034010400c45400110074201186440c1403500c8842c007001b0010680c1e401a9242c1c804030301c41e91100e6000c90701d05071050b0320755841d2094041c1205d1003070b0304c2911060806070501d00c00d103d0610a01c3c3c11200c64031802003130075044054200d05184260001400c03240419420b000c0011452091300051a0075445800544110b03003603803002409071600c0309074040c1014a0040140301d0781d440103a408040300179140d01507884100f2480d22901d0301e140390500a2a550800c050911284014003040c003425015441140c0851a800001c80881c0070881b0400003c019442000d016a800b880c16444240c802a0000c90565225180c41140c1520144200040402140b480c030403201c05128201490358101c602c51090300b4940d82607903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 422407158 1250 422405908 422405917
    0xd14010e060111150c07020f100e120a08070303020712030515011d1f120207030207030209040f020909030301050a1a031506071e03080a0e0d0e01020a080c0105041703070203 76
    0xb41448142111505203042c204032034244030419046118417403030b010b108008250040d0034102e0280c0e14000b110003075840d0019071440891495907a01711020084010007050310300c4102c511451340a4142c05c100400c002d0380091820500035140540e4440700391a28440c1e00c848213900004052502c4240001c80481001d50300c03040100340b07010304021003641c1d000012903a102c0310650303002038070a100c2c0c0511900c0b0352505828404a440701d10b80c6050300900e0f40164400d031400100103820a0005100500c0d2603109181c0250082d40d10b1401e1044c5540400d06040c42500c00078165403020004002d18604628484054440711302076102903100da20301b80e003c0d8080a0101080d15085410540c601e8030f0383e4058540464115900740c00b0110503041e030160403807c0c504180c0c00100d10314001640c03041c5500074080011045402001c280e690303600c0c01c03a0b41c1114070403664114090b0420102c0030601e20800b0f09900d00c26100005424100340c0740c0090050b03880140151030782e0062042149194001c410380c0e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 422408408 1250 422407158 422407171
    0xf13050c01050c0705031603061b05042106020706050624030c250303140606090603040308040201031d0105011503230a0f0f0b040f06050f0105070c0503060106050d14010e 75
    0x80d4481440b40549030070013086820440d050710034041f8030155482550491000c4034051681005902c0340c0e585000703900c0c03440001c41e90204e00100000c100700c00810007443d80804007034100d041c041c0007030350301d810a90344009000c0d01d00a40b5401841581e1030304510b518034158524252010254542e00c8000103404000d090f00036001d03011420070203001700c0e04844c004140350410555402d00301868040c000b890101c0401d0392a8005500092140c10b00200f200d26494009240340c2c2143d80c1d581d0125020300d0028812810140c540c1c0400d11400203400425958401e01000411250b061003034151314001c0d01c40843c0100b6040c01c04c41c0d0114615082c1501d0004484a44071201c0c0d40c40c0c039001c101034507940c0849042d062071b24500452020090b44240c90407007045030148926410803000c0d00603900726004103540a0607005c0040b0310303503000700020200180700f07214541c3d5460350b0f0000682800400d0348894003081000036000e071000014401e03000700c80c203045800c4895504002103002140b100a00340d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 422409658 1250 422408408 422408417
    0x80f03091630021017060105041404020703020a14030409110f04050d0c05090f060102211c18050703050d1701150302281d09040605041e06050f13050c01 67
    0x108040b2410003103040100b6801603e0b450003502c954400400451691001d9060b0341d0b80e260104a00e90300c500201d6003141c50749a0400c0290031a142004006d5220742012001d44c45441d86560018100b0014043c2003403c000c05140c0300c071314101c140001e807095a002404071110800001c468114403006440580c0c4040d05c804000461a00d4141441010760700640d500001000400407030036240d0101c148a4402a4250384820700c000c980c00840c1d104000c1010419982444001d820540503002412686040903002c40d542c122400911200040714074265410740001c00e040c4280041080141c1c11103005190150340260201c0003040b000744107000311004010000d0001004510135010341e02d807002180701c0c0903807503007031801e000994044490400b40030822604040006c0e0b906426051250030b4003410540761543c0e259141c00042c60000e20031100280c00b5615600000f0360780341808941d900c10701c0d001485082844035140402402002002c6040307000c001c60f0005080481c0034a0784400c01e003403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 422410908 1250 422409658 422409719
    0x30d0219080309100e010b0a15090e060103021b06060a2103050703032403032003180607051c03051302061605070504090f061b09060e0607080f030916 66
    0x144503041c94001c0070600d000361709094804a480d1819031041810000032503601c0f101c0c95651910740d1160300c80703040c0e580115989a03800c03c26001955440c0790322071030500d001440c014001400c40e489580320401c00415034003100402600d8104500b0010182902095840b01e0719144001c0c07403c80d01d00554000d00300003010030701c42c0070140a50042200c0542009200500c0350704420400050405440250b000071242c040020181e0507040d08070704040902405541b0301400700310031403070350f00400010503044001040f034000860018010040d5807420b2014580030040c1c10f40f03004060310800340400080007400010507006175101c608035101a182031036008000641802d01c03504010705580055002400d002002003000204c00701c805009106100401c001c2c00608440e50020000c2c506000108100d240184039060294881c410074050050075103103001f00c07658600c0c245821012800f00e4101d00481400380e5074500b0f0042e849412200301001264a150250700c801e42810100404d100014058 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 422412158 1250 422410908 422410921
    0x2d0a031e020a0f3203090a05060c1e0f060906070224010e13150204031b0f0e04061e09060f11040612060f08060403080a050c37030b030d02190803 64
    0x300035000304070301c4800480d12031301c1807501c07501c9a21029089101302030008011401c4c0c6001006c0c3c40c000308807140101421005452202e14020b080d08450119100c2c5450800144008011082c410300145014240d1b170305008c00044d2400d0030400042c8460840c00a043c9100041d40c4406411907480003807000c001c0c0c0b102e03c941d00101c1c4e0340b0800606600041030384008212010380080c811284107a0407812000016407203c0c2d040e17081c50154041414001008015504035814a40d40007405101d00240f241e500c142100c941a07200d18a107c0c025468040e0355041c04442d200d10f40000b15043e03028807540103003c100c4506481240110000d0180480c0e5804030441540d2214018082d1405c00c012085e07100c4550a64030502110202c1c002444600010000c054a004681c0600c0c00e4200caa4140180c2055121450344260318111481d011046511807030340f003e045007001c103061601d00040f400c0000c0145030400c3c0c841600142598083e183c1700307480c010300341c0c020040543c20403d003d0700c0303403a4038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 422413408 1250 422412158 422412203
    0x2715081b030a110613030803070e0f060d110c010c02160b1206060d0612050102030a0501120302070303050a0c0b0708191401051509030d11150402032d0a031e020a0f 72
    0x101c1104204045d5004004c10480100941c05919551103003100c8a501800b0030100d01c0040500b03a4000d0824030101c12484442d401200c0030384100f1081a08000c82041c4007401c6a02403502c0f2001039010b041803d40b5400800c0044000d840391802161a000d400d0506030603901020f07009030702034500011000c1099060f81d100300040d04030039020a505910718100680030303400554501c1c101924000c0005019200e0130303d1102d032540c0c5034001e0700c07800745140c4064403540c00405800017840f4034000709000040c4810805071186103540c0b50341c80039007014070071220300300811141c20035181e1900100c815100000170030b2504464080303a50003000d4440c8003d0620602a011185805201d19072030900090b400c8800340c80410203500464040c04100303042e0503500c40c030681e006034141d0010022200341d03800e148540042c03814117802c80d04038000010392080c5800340a2400390009280421007034444001c120440b040c0c00c0c4184010607002402e81c40b03140d03c207031078600000e0500a0410103800300c035508 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 422414658 1250 422413408 422413417
    0x614180f0405100c12050108010603031b0321020c0c09060d020f0607060c08040302010b030a080f07021f020102090301060906080c210d110105060103152715081b030a1106 75
    0x43e1a070500c0358448014010704440e4100210240303160820002240b0303400148100c40403203406d0f03030703600200702c03280e0f100488602d028030016002c00c640500c146000c108500d00880a038a8030b0400140d4a150102107070f4100103a03000007500c41c5031030806210041d42c0d8081d10a8615404481c918440d5840900180b054803551070014045400c140709440825002407540b403041d8040d400a1100c01d81810800d40c84000c440c00c0184017034002d110400030b2100c224080d040700d070302c007810110980d0640400e0b503202201c522840300050303400140344241400d0078004d800003000e800e0341c1480b15904080e1116101c03081c130080e80380549900406110000003400c050141210b0321019504081700c4140010224055001c003008030b5030900340842c400354400d204200006407240d8244455505089040d9000c001c0030b03c9a2070405036812208141d40058071911051060301b62801d821140785c2441c090078800302030080202d07440840860142a02d01040c8190a02d41c800700320340d21481c2000000d64540038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 422415908 1250 422414658 422414683
    0x50d11011206180f0e190c090c0503070509040b04050108160806011503092603040c1403060a0b0604030203190b310201140d060e101a0c01020f0d0614180f0405 70
    0x181242a40144025408900700c6c00d000f4030303404200719182e6a909054800700010600098400c00c005100a449000541025640200040781400350800040e0a50300300381c01500180d00b20107120468461005088801400103d019151540c94880d485541c6803a4500103000d05484018500810050504184090010340800070349181d1002c5d04208540048604071103d403030310302c404038003d504540174880441c0010000d02482e0b0700d414010300a004000d80d00c2c1c0d0003030f40a100100040e0340602158404040076503200180c0f5a0a0800740c201c1c09020b0044540540304026078070071a840e50401030881c10485419000c1003e0701d1004940b210740704002c1403165840130a6440461186401c0758080365205140c2d1003094840a00304200000c0c80d02c9195101240c050307000a51400c500050421540c085000504008a4111081d03c1d64015405048481d40d111003c0c000004458029001100192813203105502e80148200528802402d0311090310300c21000201009030400c07418440c01c6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 422417158 1250 422415908 422415913
    0xf0b012a0221010b10091212120e0313060c02090106080405070909140c1507061a04150810090209010308030405011e091109072304050d11011206180f0e 67
    0x1000b40d0300500810584a10b00c0c8214500003503142980c0c40b562288040d160b4006e02020110700c00d541d904c02c910320b484894400c1c01000070350000300721030321300c5002c00340c4c980d22016580d95012284800110601600b11030207003c0c0a02d07200c0301589134030ba0101d040d034816080000181e111418641c0c508111a800005c1d0142032044003c1040500315203800189a42d4045494840d004400c000000c80000a120541c4c001400328001041c01c0d5041804c488001c0b40070b1a0240040e0700c0440c040c3c07101c107981102400500b800420101404028603080d14110341d00810000c00141c3c00034940b0320062001420381400400410140b001c29401000e00040c803c1450804241c85c1e5107980c06810000d009449042000400007c0da081609403d03101e40d54aa460f803004548400449503c202200010300d14030109210121b12601c42c540090440d501078800c44141907041390004040c0d11480c01084c1c80107080c26000c0100c14a62054240c510b00d00a002244191181c181800180046010b013441031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 422418408 1250 422417158 422417209
    0x80115020d0f0e1003061d040506060121050f010302010917191109180c090103050606120a1a151e011b02180103030318080d0c0e04050a0f0b012a02 65
    0x2550554071001c202d41f102c00003c040c2203c8450000035840e0200e801402c01c1d0001c800141c141e42c80342c0649003480c0c441c800c1001c95403c54200c4041226070440311511743d05941030041c019507810200741001003001c01241d07400c0260000015449045c600d10208020300130789552010050550001d0800030805082c0c56050f203070070b22004201c002e410100c40b1043c0202440014142054a01c80d4140c90304080100382d9901c0e40c00522500f1102408800c100b4020006400c00041d400da09600c0744030060100000c0508025000c0020801401c40340c5108110851001c00f400700103007480340001e4400d0801da8082c40c203092099444025103c00203502c449440001000042220590b41c1680d02035a0104603903040e214140880c05101c28014000e82c1c0288681024150b094202401c004440d03d8851880302e08500418150b030801e0780c0307095403240c6403e43d4425091141c4542d0000103003d2a0004004480340d101c15a030407903210340003c401007111040ca082d900c0780c0c03050044040b0740721401100c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 422419658 1250 422418408 422418439
    0x604030803091c030b0603011802040b04150813020f0d05070906080a0611070201080112050c040c030903140a0c03110a0f03020d020115051804050f1c080115020d0f0e 73
    0x2241d580c212522503000380e1543d0031401c80c1c405c0c45a0900781c1c00c0603282501d540d0801c2c00352581c000210b8250b08403250200004a09128494040c100920142d8001c08405010f5907000d0140c0324028a0243c24009281028002da510070203022503a5a06550304e03112020141401400e049058000c890880e08088000410000c0021402540e6000d55002c010303000340d59607900e400d4401c0c20305c003a0000300c1d510014040c1600407504003001c1c03407040044030102c0305040c2c0898141d807510703800440840c1e518010380e030a05810007958240209800c1000b49040080907014101c030042030000b03000c1000c00c50000102e00820484210351640180309112507003161700d0025511001481d003000194240030005801c00701080d2440240c0b940180a0f081e81002580e845180e03c0009005031107d116419007800c40000920141012022580300006188a000c101400804042e0f110241c00643c00501c5040b041d40400c0c4480103604c10701e0100300141c0c0021b021260b000c1c258a84075400b20b00c6040c10040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 422420908 1250 422419658 422419663
    0xa0203061509180c120319120c0903170a110f0610060801180506012606030705010c0206190203040810050a06090c1409040f020f0a030e030c0c0609060403080309 71
    0x160550488004600c2d950703c1a651801c0841618081840e80c0300076284907a500d880c0400c8207504100c0380440341048000e120800c0440825014000458980e41c0102140921270045405840b120704104249600d0b6903180c0511109652241000f400041608840ca0f482121880142954801100c00c010140c030340c0103448190a50b02540244020b81000403003a005a000b075040f81e960345a40e1032803190a8401c44080c1100800c4641081204540c03c20301d0000c800c007140700180c1d026103883c02450401c05051916603036030000c03414045408903020040e61040e00722102444213120100301748031001000d07031a500071600070103a03d0244030380414000300c195100a01c0380c507801400b40083c6039070314a42ea04541030030400030300103920508a888400340440c000d090100b0082c0000039003888190610080b0f8203d40850703100148000f80344090644d05000d1240c1c5c981d414405546400e80800c2c4891b07030740b444655554080c0d54081070012543e0360702003c2e1001103030410b09440e620b00e0100b45258 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 422422158 1250 422420908 422420941
    0xc0d3201020a08180a121e030b040b1c0f050309030a080903060601080106020a140708030a1e08101202030312010e07080f070509091906081b1c060507020a020306 71
    0x300091007080042c41804501c1000344c0954541c130041d0000030040c3c1c48112601815907a50300601c060034a2481c45200b00101100356200c05a8000482d5880c1c6010007041e20f803e83c145600c10505c00d2440c5c00709880400c41948081e03480000020031700410301d0b0072070442c0a0021030719490f002e00c0f40a9030911104000501201c4c40c214207031400f5603116401914015028090600160321507100d410008103403100c080400403044045806403681d60001394503580c445100e00002905030103511041c6007807080703030350000c0d881d5080c9030185182103590b0ba9403814040c0310b07260780d840d0215481001d40d01d00340110f9085c14191400300d4980d68550b545030031030007001d03180100010f01800004000300c41c01429580508500d1740e51914002a102c100401c80c80c020b001c4000d083c2c0054401c0008109901c284401818004090a0540d0804020924002c00c001d111030246a0950b40d00b40f444101c2c0304100901503004e000040c0310785641c10120b141a070004c0c0001c1d0940b1404080c040380d58046601c24 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 422423408 1250 422422158 422422177
    0x303130c0501050f0d02090109030c120302010f05061f12060b0403021c030f0c080906070c1809033f021e1602121c05040501030e0c0d320102 62
    0x384011560364004442a1240c0c1e600741030b200b1010310094120b060a50010414607005140040c0c10a03280c0c1c0745c0d0006060681c1c010500c080031150400100740d0207005218140c06143d02c100100e24001021650241a0012074207060520403100ca4105020345810310655070301c040c0800c20a07071100d04040b003070b40c080e002c180e2081b1404c0b030f2400300d9005c2d80c964001c092136250f950f04684589240d0240c0315441992412039042c01c05014400840d00c2e901e000c2d121042c0940c041031011807500f840045003108007410039155504104e04803000c01e80200c86d06032044041017000113020300041d91490705121010002404c001c000032341641015180c0c0103000d03c150100714101421b2031903600c6007918440d5405030404940502d60b032001525121010b071503455400b600765040407005044000e0408103d206190119001240c184041e5030700d445100c143e03901010080042c0b0620000040300802101e0300102801e620030702c091455406000e40c3d40c081400c41ca4400ca28074410b4030b5240c00b0b90401140c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 422424658 1250 422423408 422423423
    0x15030308332b02100203090d05010c0e01080702150a270b15090412020a0503070b0f010e01060210090516080604170a0507290103051e010204080d0509040608030313 72
    0x4020032254004485210760b407402c44203162070300855082c4944403902039403440c19800244411101610303500e608451092180c00006580900b8a20140035102407612450401280d0001c00902d40d400013030b5443d000c210086e50241c150380b034030f085d0b2010f050f03100030100e807010a0108010001102034210301010340701d1520602140c1d2004145603244100801c3d90f54000701d19008a0041201004a171640c20314500c160340c45a100350716000d146901000080310f8124651003000034880c070941c40c980c05404000c04150455150800080d0b441c07541a030150000380d52800ca48040020070042c0050125a9280800d00f080e0b03500601600c0c2d0342c01322070941d901d0b811105e03041d034005075640840341050000c4d00c0d1141030070351075110800c04100c21075503400942641d803903036034148d0107070a0194000c5d0b1184006014050340b024802c0904103924140b4141a80148000e02001c100801d0110a500d02c1d81f40098a400301040081e001d4120380d03006461501001040c08100c401c41418640428001c211 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 422425908 1250 422424658 422424679
    0x80f06150a1e03020c030726041d060108070903061517010c0e030109030203041a070c030b071815050f0f0c03210f01090e0a0210050a0306091503030833 67
    0x30141d00380d100b8480c100e9480e1b0802c0012600048400440450300f6200c00d0301c0e10400d040383e980f8440d06610503001520f002c40da0100f00b070344540304a2000c2c1d07032045003843e013010f8134100701a01030705140b40e500008000584461624500307100703081c090001403140b4400c86091a401c00107181c001c000c64801000014039041100a46080501500c101e0b50b41c03550096160510340211800707800b200303112407450b04000f0410309001c1604504020061405591f04404c1810072031340181900b04960901c000321346400400304014038100c1500700c0486050b0622540ea0b825130b0007180d0051050f001c081f0301c44140400c9540c0080000405880803009101d10400340070402c00001058a8089502c48112440000103010300105078000e4020225001d0444040359481c1d40040d07001c0e490f146020b4000790020601900b0190306004100080050341e108000300c04039200380100d009030703500016082c042840c011400f1414942259039076607040305000912040000c40d4080000c00092600c0d00c246103404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 422427158 1250 422425908 422425967
    0x1060e010b0307080702100204060e0f041a06030a02090603161b080306012003030f0609010b07080d05090a020306100302190b07060c03020c010204120b09060106080f06150a 76
    0x40099060310040c4102600315603900d6004c642a07500109844110301503100ca042016609001a0000e4142ca4072001226030b500b60602002215440225210b1400d040082e440c6800d040f0142443c028190342c2140c0c2c0e0342c3d41c074900074080c0c814800343d550004400820003000440701c03c101c4105060503903450a241404800b10403201c030300280c0c054a40b403810030224890b036006e420380348141c046154090a922200c102d0540c01c5401c1111106d00043c2c1640070444107140100020b4050002c12081c1c3d8144505a00e621030240140f442d441c1c0c200d603491001c0f503000b000c20051203080340c0d801401c0315884e00d4200e202c2c04580800b848100d0140c0c2010400c0c8079a500d014107400c3c15aa24a40c0c2503040c1005500c03101c0290645c0f0407030005165003000710358a020800e00081001d80b15035111441c00d11054a45005030050082c815000c50f080000144012540008400e4120050f111040a6a00c40c000040c1c00040d1310b034000043c41c0d5000950105c500d4100d884844445000400c11a1489010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 422428408 1250 422427158 422427179
    0x100b03060609010909050a0f0615080d14130f06090801050c0304030f21020a031a040e07050918010218191802070c080a0c080601090c09050904030203070b04140106 72
    0x41c0c0710715034011450001030043e8404c5078020b003007290251044030701d849403030707203501068002001003034402d6511075402c5481d007107240c5948801491600024032070000c40030401420038032009004c2c442c504001030700c01501500c0e0a4008042c00915448003007180d41c542015000381c034203101e002c40300d5003002c0002d09001c0d50034040e6481a60517880380303548269510401c503402040310100c2201d440d81580a20f5032404184040c0c50b902c2d1098a0005901c6400200c8034a0380d180030740128030950030440c214071201f0010518500301e41c0242c03202c2c9034036280c451124036a00c0c944080c020440d0b1010680031310b0014a02c8810008040035140845165040c46d02d26954a40900605103812510741008480600c154010003000340200c441c254640e4941102a05000c6ca0000c20784524550220078130000105001c454010103501e00c040240389100d82c4043c003151000d03c107480c031400100000805050007803044078501075002080705641c1c50b1525003200c40ca000e42d407000311590f00c1c1000100d44008031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 422429658 1250 422428408 422428411
    0x80408150f0c1b1e010b03150108070501030b030a170403030e0303121f05091302150c0604020f040b031f1503050a02060d060b03130b06010e130b01140c100b0306 71
    0xc1c00b1000745400441e855020b540610002e4208480c4590100f507000070180c180030b07092010b50304001181100560081524150100045008042d48200100604000041c406080b61000e090204010008500090400d4940c03030000e8001c649000c03420310340e04920802082502e100b1388a80b21489501c130b00340350342e034060840d41c00428820040030854041130030640003984890b8004c4407085030b44400124820481c21368048444007140d030300140031468800240210000c220f0141e9050202d040b41c1550780b104094400b0b030091808a0004440d034649030810701880c0e00c00b50454110300702d6a070361145820174a0b020703c0f994501d801800c0882450f041300c0f1a044a80110045c06003850607002c01005510440250288940d10f010000e00008040b0243d071149084a00250642c901c0d41403201c0e2503400106940e0422903140c0d03060000f581c80000009007200e0b04940001c0c01045c50005807250740d0804002d0b00c5079040403510550000c0002811022050350540c107100d150750980c02d03d50740c4c800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 422430908 1250 422429658 422429671
    0x316080619020724020d0603080c060c0c1506040f0203070503070906110a0206030a060305070806152707090506040803090315040b2d10031b03081c09080408150f 71
    0x601c08008010352001403c0d01004c03a00900041c0f500c04022146000c407429035204880d951008070304034030000800d00c007855100311220314036460300103002e00058440d0b0942181d001e0310070354000413070055190782d0720000346806084000c640d01d00788420040d06c03642040f2000c10010700c4500c404100326205d502e180003409981c800402201c0c286a00b0069560402030140800964420001000c50f00c01c000d000d009001d164081c000b181030034901c40d05000c000f20b1290740920700c0c1d1f51a044405001c10040c640994003c02c0c1c101050721500c4044950310f071151321079503001c8808280132400d100080004c00c40001c0407421240c51862a0004003107030241107030082c10380d4840c4000509800d4402a42c500b84000345176015450401d9000c0081003424213903018090582d03800710500030050300c006c0c0d80c001c1201804000d5034003441d50342c81c0085441b070800c45c4404034130003445071402c4e82003982115001c1680300000c192120b4880310915912240310301181c03220303030910b0040340740c8101d0050701500802 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 422432158 1250 422430908 422430923
    0xb011403070e01090e0c10031e020a0e01031a030a05060115140306010f09120c1a03090a03031a060712020105010501321204050105040b16051803160806190207 70
    0x30b01e0f001e080c4c0c00812425200500703a0007100e002c5816591000340310340c1401f80b15100091800640114001c0d030400c0d011100040038030411284050941084440c62003010034600812040864030044200c0e0414408058051203a0141c4004214000c241d09050310000c1c81780c900f404088001c200c03082c034103c62031096140c0d020000718405520038200c02180c07201c141400c1903480d50340ca02e51641d082c800707074007515030400030354042c032541000303500341c42000d4418004a81035040c0f45060a03112021108010141651030072003c40c5c82c0e03407140c80754800603001880107807035801c6030900c2c100c102c0003403e481005520340130000c00d8039801001d5400088030740401140314803c13a03803c1c0d0381d00446c034907040307828482050040c00c402810b0303030079010b1080f0700c03a900224007410729280c14400d1240141800130b0b06044000c1d040354032a480010740300b049004242e480c0c45080e0700d201013030610240605006981c10381d84808036002c280019440e0240a5180300c0310340c0101503006a400724061004001e0510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 422433408 1250 422432158 422432161
    0x50604050601091211060403080c06010305010605090402101d040f150915030b09211c02040501050706150b071208070f0c08030613021801080a0e2e090b011403070e 72
    0x205d0f50410207640304405010075190030303129100c07a90b96030807106002000c0d6020100501c1040001c0c001d001c010300b41511952607a0503e5800126184400041d16040122118031586580c602c28001c044080014004024003020a001c0030050440d1851114151a900500041c40c3c0040d01c10b0602d0310030310303207514220a811a5107881d8105d0001d00951000c1c4141410f200b0728030903034200030581c10462102a035031111001350005101410341c01c40b034081c0d84144410011641c106081782c061503072010001a0b851200e80f084840c1c2d180036001425614000b1603410100180f60204040c20f0100342c80341805035544040c121010801c50f20043c0000c0c240800900c00550b6410140da0400303801410811440038808611080385c00c00030301035100703460021015240c1e50300101081d03005410100c09000c00c1000d42c0b503041d80c40342c1c0705120050780741d21003444104038042802e800811614280c0280200c01d09810042020fa500707010ba407007002000800e500507868005502000c40b480381000341310704d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 422434658 1250 422433408 422433413
    0x290a09050a1e270513060f1103010501120212040605100902042322020d152d0909060c0f170601110c04020c0f0705030304060203180402120a0506040506010912 70
    0x320641d640d1a0016400e000500c403042030a0f5020b054420b003096074250880d00440d09160041d2003013040c40c1c04060341f4149841810284000c00c507030544500782440c583c452102c045030030003072203034074400088410341c40107100030400d00b500028010725448480841c440d4484040304124402c1e482401440500601c0d0980d44200306900b084034558010006443e00e06007455040c03c510580c000307105030700d17400200300000609030301c103403540740791000c010f00071550030040701e0b08030198400c1641c048450b100305401081501c54031150003418003004140280c1c1c24070300e403000107480700e05800c01c0401c00380064841c41c0c602c203c2580e50f00c90004404d29825803a8a80152508000034120621078095002044210740f5140002c0800e4542c0e10b0080134100e8a0101d41410420141c201d40c1c86608200001c01c061540001541c5e595802e50400008100d51400001d00910484810b03c4858108000700400080503a021030710500c8241c80c24003042c1d66040045941d58041d016000314a032040c0e448201 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 422435908 1250 422434658 422434679
    0x5061017060c0a031a0301090b16020a0b0408030c0c070605040f090c120b010504080111180d050d0f020a060608030304050c190306094b0804290a09050a1e 68
    0xd17841c510511100c1807074811021a09459111100741c03250100c61040c000c0842a2004900c0300c0342d000c9c80545143c003210f035200450603101520140805c14080081501c041e00c00d02101c1c06164401c0c11140803503699140034000f03070030902c10010780c608031220020f0034140318010003521049aa4a084444105104d04802051501030742410858184004680c501d400d1248100e1040400d28242d20b9048840d44041400c1c040c80740342d40521402ea809000242000909c0000e4100314140200460642c0c1412460102c0401d00588014240750001440d1600030005501680c0141c080d00e40e07504c890414404602c0c05645040ca400308080d0040001c50300a030b001c02d21007032146010521001c1e076900301c1011818280d2105580041040921520824a2001000d0100d4040141c05400515200c000030750085102e6000c030407000000081058a081c0110700c5040302d050480380d10f9030100301c0010181840c2c0e0042e1800344032481c2c804500c0b50f102218008403100d052a500742c103113003029450f00b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 422437158 1250 422435908 422435921
    0x1206060819060e0f01050c09040b0609030a02060a030b1903150c0e01030908120408030919020307150c02030d05180303190c020109030b1510030b011706030a05061017060c0a03 77
    0x30f60f000d02440200c140a0030301503140500d40002281d034072541c280007000f084032a500c88107403086a003042501c0c01518041010460307103804558268507601080f0040e0302804804d904d080d44270110000c04000c00304003031001429680110101d04594010070030baa01120f61901141c0007180e42201080009c2d84a40c010082061003206030074240356004440121404080c0c50485529030003008100402c50108201d41800c401e808a0f203180c1c56017600440d80304d066500594080c4a074401000719014084c0c50300520351a80a41181c2001c4000ba00080c400c0c0c2003581a03000d2521404018030390352238000280c0c2d01045092080301d01c003141c442800d036145280100d0480c1806100d00c0c000012030404d11200c1d219001601c0ea41c40e84400c040104181c1d07030700500c014401e00d490708001d001241d90140a80c0c0c9410540c40220130b140d1604000280b03000c0c00000020064400e001c2000200c10403460a0b0f02140c00d01c20139485007a03c03c0c40e002e0303110f144c100c4e4000440c020034000201039038400c2c5c2289 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 422438408 1250 422437158 422437181
    0x192d1409010915020322060614090118111c050f060a05011d0d02100806010327230a0f0b0603031c05060a0b070302060403120203010602030406120e07120606081906 72
    0x30182c1501b40c4070000380c2c2075803443d0685455940f80c004100f1031950002050442c80111502e000703e6040c20004007401c04100c20700000c5560311440400040b40c0c0350210f44819250b034510401054098080b400501000c0307a20030300c0b054170f10740421310030b0800c0b040e20340541788141c4813001030b00780c070f403480c1d00c0c0d00f428802d240c1d54000350006001c405038407001100130641c0700c0350341d801146140c024000344c00e07039078060f109601440e21800000034050038030189130504d56000e540080c800082c07403c000c6031032400c1810344080b0701440303499604116107824030052042c030884013680540da0780c400b055103c1c058910840c02c44220103108089040c456400191b1040c8000c00540540b91142c01e29022500711510071405a400b19040c4014103410180c200c0300010502015032a40d030501900030740320702a0b441030206000241e1903d860b410150b41041000045c1c8204a4204641c0c0b012070710210300010074161455031401c0004038a41d0030100b1141c6003004c8003071036900c4031005642d410300206112200c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 422439658 1250 422438408 422438431
    0x10c0c03020a060804120806010c0b07031d0d0806190e07020f0d0f1101060501120b06040801090605040b07090812030c070506010906080d08192d14090109150203 71
    0x100c01030760740c50034000c058400c035a01c1140616151410000411552020301c041c09160010003503541e90080e00012890352140c0303001030a441d000c0c01680504400424020700e9250601411440c001c006080318420b8081c2c0e460341c80d19102c800078080140c4a80b2a510f400b03205180c41030224140c2e80c000290000c0483c4100c50784c000101501c01c1c2448030481c54000040c05600d400c0107841d40c444144404504010003c0081d58508000a4500c0d2291880e40308440d803680c0c02841d050351500240c60040a00d00c000380482c1e141ea03d0044002c04c0c00f00c41c01c8903504c140c04003080c0e442e0301c42c41e078850031f0b60110801031000f4544030440c44000e40005201901d03190b000c12130400041c80c1800b0a41c028a29510040360849c01c00d01d0300d600b001048820302c03040010769001c10283d041920300e1000740d0202664009a5413842c0360880c05858444001442d092a9031305802401410740c1d4030030505504c0311052a060350701d503005824240c0d180e102c5c0241a00702c420004449081c156801950410b404012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 422440908 1250 422439658 422439683
    0x20301180917030907050906060c0d14070609050d2c0f04091202010e0606030a03020712081e030f010e011d090709061814090601030807020f210106080c0609010c 71
    0x740c40362607072088a0031031990300a540104551f041084101d0f401460883d8490308046001c11183e5070703600b80101030001c02100c0e02c22414650040d00031900b86542009082c0205841810b20aa0b6080004282c100044400f00e401501c4003000c4051031070840c12840341c403114040d101c20445440600e401c1c90780c1c065603407246040043d0003989040707940c4900b03400103d001526000068104003000307020f80c0c001d1304040200c00000e6030214042080c0c89a4405404040403281002c2d05640541701411003039074659540704502d02c401001071486070003000701c00d03640d60303880740b80f102c8401c10700388184060202910f0041d1040e0f2a115101c0d9404441c0300100d484185d6103903e0315003a10700366407001642c039607100844c2000c2130072401140c50075801d101c10342007581004441d0996075201413201408012000c2140001c650700e4400000d03002c2001000d1340c2076a0080b69401c0e00500851800c1e1115601e0300b00c0005508002088890780708800610060070b007071f201001561010000c3c0b100f260715400507032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 422442158 1250 422440908 422440943
    0x2041d0c0a0309081b0a02090106020c0d03030513171213030e130b100e0f0406050a03081315030b01030c0309080307050c0106050d050a05060702070506040312030209030a080c010c030203011809 85
    0x1405402c644945c48020f00f0040e5590040c44404101a000030085412100840350251903001c0906c01843d81440e00013002d5890001c041e10701004030000428841550f15103200d0403541001a254022503881030002c5900c038160340c1c0142200d403a03402400705102c8400c1228900c2d014600da9806102c1103000311f00070b02d0400001d0428103201c000100400e5030106800036900b0450702e940c0002c0820742d020008241042e0004105880ca13100050845c8400140f140f2400301d43c0e50100e00a000200303d408030341c000e0301d2014000e4110b012030700b40000d280001c0c0304070151180c042c00308815040a41545940c46181c01124a58042114040150f4843c0d83c0042c090311544e00c03000a0380c0c010390160140c0141850460300740400076101d0b104551003040305000e240d54804c02c40c4c0450ba44a085002c00d0b011400041d0040e00030624450340c107010355520703003040c410004001c0c8010510b040013040b00c800840400d60881c0403e0284151110908040341d03400072a83c1c0c480e507125801083c4039020224501c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 422443408 1250 422442158 422442187
    0x120c030c0703260c0705040c210c0e0301090c0504242c010303080f04150e0f01110f180303070f06020904060905040807120e10020102041d0c0a030908 66
    0x181d0048400f1020344082d02c29001d0100c3c0070881c1070744407038003540c070f04101c1910040c0c0d581e480d401114804e5076107165900d00d0714080c20b5039010980480d01940e80329002c400402004001000311360300850ba90b10150345141c17806105103202947c3c42201e01c0084e0b41404280001441c2c103504c120281c5107804800000601012034000007005008820f06480d00e102c080b01101004060b66001d40d100207800610000390415501c0c0d030311000d651111021541c607800c00f000c46e81101300414605a03e0010201003081000c500c00f0415944034001740700d4161880c40c5a40c00c1c0c0f140000c1d2303a071542c00c01d0004912440703103043d40c909046002004c403810a102c40e154055908200390341122840c1c2c0c0010607140504203402044001c01071007104000a1801383c668140c940718880005021103000021030743c4a81c00b80501c51034103503000d000745000100e01c0501034003e40c4107024151080000030035900080075a08940c0340f20700d40c80590503042500c442000d81c003601411a04a40041c0288001d03c044800d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 422444658 1250 422443408 422443423
    0x40803040b090415060909180812060103141e130501020f030a0e010b010c060b0a170312010503010b010f0c03030608062706060a12020a0905100302010f0203030702120c030c 76
    0x48803070103561460140200030444500042c044448a80e0000402400c1d4011545804581c0c4a0740040349244c58040007001c03000720350500402c90342d00403424110703840e06020454030545080c1c8081200484204c140b5410b03140c200c0d010382c00d00da90216603003103c0d40c1c2c0d4841c190300806480c200c02e440d00503942e209800d81c2c01610311500800d4002c4100010144039018031007100610200070080515444002001180802d101818150f140c54001245454081817140103106018011101551b1028599101c1e4090050304c417802001100105580c034043c070510301350140c16118108000c0c8120700c265100340c4110800d8047c03554070140013503564414040c01c1e03c0396007040b040c1c0101e0b40102c1100c4204500d00e08a100169004008106058a980d04601c0c01d40781843c44400c281c000d10303c005541080b02e40c1003818414108070900949103285800701c01500d101341c84103501c811403603004030b9a0b800200d5408005078095810f0b400c00b08180401000c9805502d405d407450b0054103840c080c50700a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 422445908 1250 422444658 422444669
    0x901020c090f040516060e010e030c0901030320030405060405150706090c030308090c03071701060518010e010b03070c0605040c05030a0b1b0a092102130b040b0409030c0b04030504080304 82
    0x42c0c841c10002003140034450440b500c46400b0032440e80d9400e0200c0144410b000580d11070510a4600741000350340d500700b15484403140c0050400d626980c403444d000b0522094254810344075140315001d04202e400100944040e25030140800d42024034040401c06071071030f000b40c001c034180e004000340804103000d80610b04085001d02c0c00b46042c6491803070010229040200420030a0b00410322400859a0100d180c908803211b8184402555410b13911090042c4807546c005503000004111010f4101e00003d8214100c5600750290b12250b0b9880001c031241d48000c681d80e00003e28080c541e00d0002d04241e000d43c0d0024003070808007080c10f882d0b1010034030703000c07501600740c03000c3c0241001c00c40d1401894401040186900e030601d03041504401018000000c54000d440000f207101c0030f491110107160040761010b5400900802d100c842c001801002401da07404041d010b1030a04c540303c01c44c1e06090040600c19035050307690440300509034407074100c0c3d5040503004038100034003004000794a08003003024001400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 422447158 1250 422445908 422445931
    0x10110a03032301060f0c020105130906050a05060906030c070510060605120106031b2105010f03140a0b040f11120309040e0a0b010e0a060305011406011709120901020c09 74
    0x41c0340019889a140d103a02c40c2c41a9a61503000501038203500c00116400010581001d131091102c87c4016543c80c000c0ca002c078003404130820800214140c0a42090b000c461f026150002000e85071000c4c02a644240901242c00020030008110394800300c40c000c0c0710b128001d1082c0c81c0c00c85501e01c02c0300166200b550140000440100c0d03a0016403998402c1c035401400796050401c00301810921081c1c882100310141d0003071154465202c48031121440e14424480900d4030104003540e1600c0184100c42c03860301007501c2c4100414642d08210000080181d10503401402c205095aa982c0d10070031100c9203040101c6a0260304d025610140d12445c00a981008041c2c020310744442118080c03000f00e5100225500325984041c8809011501c02049641915124856002c842c0e684400000140500b50f000800540ca006a002090760308206140d0142c0e100742d80c0c42d5400e007285d8a8890710781006a4190380700d80c10141034507100fa80c4c4600240100c1006005035401d01c1100c000151140600f1502c43d80c440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 422448408 1250 422447158 422447171
    0x3050307060506040e011413060f060f060f023d060f052407020f220f0b030c0f1905060d02030403030509031602220f06080c061810110a0303 62
    0xd140c18000d001546a8101c007c02184a44080c0d00c8418403018000794000b07814840c100090047d00e4014030b0003c0288041406040e030340e07107086603640e551031080500213484c12981801c0c9900c0451004803020401c0b01e0051300c007210010204410850001090a603450707000701400807102400b03207100034035426100c0700c3e00d9441e00040c000d000c200e01c11251304036214990305c81d2007606c0d04c0b0240c07490190191045800026180041166000d032810b03010103050b03150340b01d00094682d40e0805d0f030300590114001e019200171380d414075564140c900c0f88907502c54401910712601c4d0401c110420011160300e10f40071091680c5401103080c5c1e9000131201580550000200400e041d0903000d401e401c0494103004500e8a2041d0071401c0484450b814000d11a444501c2c40c100c20380d958049041161007424810806c01401c1501580100640c0c0f0071001039014400c00d4603080d2614406850300d45403400000740140075510104581d200301c600038072040c00040010040402d42c20816a8404e034401e07140041e94 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 422449658 1250 422448408 422448421
    0x1a1b150610020d02030f0c0a051005070f030902011b060204050a060c060e0c091f0b0307020607020c01090501091404110f03040c050a03081b0a062f0408060c030709030503070605 78
    0x14500110a45055500102d0101100350b80041106e10154070b4039403154480c0301d4900040c1c1490803000003d0300c144600b188020040055038800350007410035031108020361010b0b260540036912460006808540360b800a51001ca070007115030441640300d03443c0140b8064417440080c40c00c110b02c3c0c10400009415071348600030084d440c8a01c80c04103d04000034884100c050b400640511001004901c1c06941510300742e003004202008100a007003075201403500d901d1b00000c02942c0d481b00325205c100501c12844580c0f00b0f54000c14080d41905d80c1a540c5101c601d0500314903c1c22518039082d004d420568405210641079244c901803c0c401c40d07151201c5a5070f080c28185510100040d80109120396103031442040001d05000440d1007004903242e940728880701c0c3c000741a05210b03500201800395814616201d10080c1108001c410810444003118a00c3d50118807005590140c2d00810a00b036001c103000c91701408881000c0d6501030a20301e42030350140e07220356615080d83c0101c00c0c112a09a12203042c0440b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 422450908 1250 422449658 422449669
    0x50702090a05060d030c140109030314070f021b12150414030918091501090f0e0f07290a030204090b0f01080402040209040212010803221a1b1506 64
    0x400c480c80038010700c850b0900c500000c2c031480304028000c3c18400b0303151b1002c0070000740032803a11070503014800812000525003800742c05005442014110300e610a4002803006001d500c0c2824903141f154000c0c02c81c0741400b6001004d034080c801c52103502c24030840304001c0c03c3c10300b04102c0c6520075241c06810f140e4246071400300440ca000c1403003600d03250000c5c09441c00c6502e500c0591207000d00044000c0c02c494071031030f034414209800c4080c0119041d03030313600c001b060700c1089402c81d5201c03858103c01001060390401400340c94880400c18000035400c13000c0c2c100a00301105e8aa41c00b25080d100030406c410001644c0010715601841d400808650041030070000e1241c50b1040301d090090594030250400b0840b00002c002e076a000340000d10440d80414880c1544d2074030350550b0080d1150440c0c81d8110350b1204403280e56030f002041c1c80110702c070036000100c241106141294040f151014800710320f0a90780340c80e4078484d4214400301800f0881d0031181b01e0304d65001300300045102c0c0c2d20003881c00e05414100113112 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 422452158 1250 422450908 422450911
    0x506040608030706020a021608060c0711090403030b0a0902090604090906021207020a0507050f01052704090f1203060305030307030504030201020d02041518080c040e2b080105030d0801030b0a0b1005070209 90
    0x4e070b07d0820300e0b230f04101214011403207585c40703100720504966031000e510304004184600120b254109008004003c02c154250384110300d10030080300ca1104107561000150282d00c56014200d806c81d50611017000f4101003504024800e920070311001d400d1110701410401101c100729a12401a44021414028040305108001c003820040e00c4418104031074200180403440b804a40d1002c012412041c2c2e6012500e03a00414010040100103100d060441c1c145894000151107007502e800307a01e40d070300c600400d0081c4911400c5036440006182144e5542c8002e400506000300154103554080010b0030700d196845c4024005408203c0e85548503801104c1d00500c12498288031441d4800000821700c01464006001845020b040720085800d108140d007250400c4405200c46034118601000401d40030503002c032142c1a000e103940c1d1110503a0380c4508050b0350f544210641e40200e078400d0018000b26407001805030f40f00078420008654010020086100c0c07001d0400a540001d070081400000c5140962506 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 422453408 1250 422452158 422452183
    0x70c0b090606060901050901020109080a050c01050c0406020c0114120c07060f15140d02060703021c0c0b190e0724230319060b0409060506130303030506040608030706020a02 76
    0x7803040746072401c00b290803032042182c443d042c40030100c0c08403031981c0301350005d104256003d8903051711854001c0340901a030300f00c07030340c598541d5091400103412124120151411195507500030701c0c0c0e5620030703401500c2085202e100003030480010031001240700701740d0a075640a8103084c05410b075500c0c82414000d0803035800707060400c1c40e40d003040c00f004100b100240592080d070300c8590389807101e0340031500041c1031030b04c200c44000d4101e900031403520103240c1c010600c1105150f4031002c15098842c1c1d0403084440105410008181100b40740101c0d10a044155014401007000341e000200021503034030f00d600c0d04a16a01c2400b50642040402810295500c101c6652a0300747c2440000700c4a0040c1030f403c516410480c401340e5000100004200c000d54440e110070b1003c000108010642e15101180b47c1980035000e45100c83c0d0501400042d07600380081100e80c04580c44650908241c11540d088025080c00362034198096115840416a04021300082100d0b501c00d071801681c4d000003810107410011500c054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 422454658 1250 422453408 422453413
    0xc07150c0c06020a020d0b070e0301050a0603260d0f02090d26040e0117032106010219110906030102040b0d05010e0609100e0903040906080303040209010b09010e01050903100203070c0b09 82
    0x7031300e005031541c803c1802e880380d028102e004c450b44c0b0804101c51030500a1a080c0c8d1540c02e0600744104001607034011803e0301d0003824141511170b4032085580d017615509202400000041118228024107a4042c40c0d2110000d08003500d0007a034100045d000040c040c200b5a03581911111526445030a40020902228603942c818186440c00001d47d503150414480c040d026104003012002c044402d00480e40e45080500e000701c2c0d0b020138910b0b681400c0400b190710f18058802c0561850340c80c2d00f05501d03058842d520650305400030707448005100411501405058156400384801314600c89600042c00860030602030024196150001d09021128090304140c059030b907002c14071103600340092070042070b1095110000010703210aa1304904d03511841c0e0140f9041858214042030f902008401035002c3c80c02250f40300325503603c510b00d02049115030b038131140c045640076029112950103040a0410048010261015801c2000200c4261f0340211028000030b05107a100c0d00806c091034100c40d0304030310803400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 422455908 1250 422454658 422454673
    0x605090115050c1501081c0822030c08040b0c011a030604020d0804080307080307030e07050906190f0608090d0e0f010507060e0f0615090603070b0c07150c0c0602 71
    0x41003a85a512101c010412a0024040700100030030400355400909880507040190303581c11032507444012a25040c1601c590202c940d800c0307580300d480c0c1940909074824019020030040680d420036200e03c1a0124188002e007a03100b400702d880d0501801c01840c0c00c4581c1650303408140441e5003150f00c2080141e04800c4900d01460701e54030000341103030348503506649222030407000341041443c138004c55100c0c512610000914404000c6040065806004035480034840017801c0124103443c0c100a0003001d4100780c04000081461800c038040340400c600180071002015181c1c3d0440311940d109404c000041072501c5c0501142d0001005118100499450301c1d4400c48084000910840c03281d0700400d04010020880a0501c071550740304c0140d20484004881d1b42214900700d5a403114021241000f100c16171311444169804c0030f00000303101d100e0044c0a000401c1c10034040e128540c00c800305039001d034071419101045001c001032080c2e29801c20781e100c181c0c0c0142c0c1498400c0c00e0001e20340000046412041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 422457158 1250 422455908 422455919
    0xa0302030a2607140f0f0a0909051902160f0f1e0c0905060604150801060305060a0803031f051503011a0a0c02012102040605090a05030d02100e1507080a06050901 71
    0x1059a00b0290364a000c0309518540441360741c01c1c1c06034209410180100182540e01034003098000c0012601545a2041c070a98480120342180e10458500c441070002001240505002da8010908032034a00351140f10103180c4d4071060302c0400482400c030390740a000560101400868111049404d0b1045c0c0d120900d46002ea44d44054440f1034460b48015986443c08207605684107410355000d461010700e44d4101010190380104080028468400803038034240c007152207030601c3e07070943e009d0b04d40d404004c601d981c40c0e4070310821280d00800c1c0044100008031602050940e40c00110041d45600c9044143d01d0703504180c4000c0c130441c101140ca24000e031040065a0b00250001d9504500b550242400d00c62502940c0c94101d0802285070305094080c800039011841d150410058084020103a4002c1181c0f031b01c6e0b10038140d40b4006020100f0140c2d000000410960ba031641181da074a084800c01d850011403003510683c0d01740d42c00e6840901182c018005c0029084039071188000a2400319031000c259413410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 422458408 1250 422457158 422457227
    0x3010203040c031e082206050f120a0209060a0519030605150a02011103090d0e04180f11090f0f090a0c0504020d020408100e160303090b030411030a0302030a 69
    0x502c00200752901d1203004680b100c0c1e403161661016030308a05c40070754a0680c0c0000301280e141048600003011084000499000e02c44e00c26030b600c00d00b0082d0002c0c42c1290700d0400901c1c0000082030454400d07001c12150f6490340ba0307a0040c0a41d9001901c0b0030b41c6908460302004041040592441d08040c900402000b090703440100171b401d081a1f60306050754a08007000c0803805031400c0c44e6070459040340002407154030301000400e140c2c1c20210759201c02c968954030041109a84030500c140f03400c1c41a0314203200105d207800500b61030040c814001c0782d03014120340340803076400d0000300c40342018840d1142c200300d201601c2e40f0400350702c03254003009005150403e81c0c898041c9040d5000e803500465020400b40c404106680c1103801808105d000c460001c0e00d4a00000080c05082e481c9076694040c00041e0600229110713a04010380e607140c0c9844400038100702440c84946c000030020395003c08101c480c3c12554500703000b04c90410f4041e6018655131031300148003900303501d04a1482c02034804660030b05ca403100e100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 422459658 1250 422458408 422458433
    0x3050c03060d0204140103030e03070e190c053a09200109080f0a02010201390e0904060e0d050906030f090c030d05190c020607111909020310050301020304 68
    0xb25001841c0c00164004140201858099255003105044c0048181030308004041d4072030504034121060581c40d541031419500054990080310000715504800006081d080084d205003585081400c04580b0038600c6030007424248540b10407075113450541d1045801100c00d05128100344d905000849080d581c0811410040303560340141d42c40c054900d23010760710030945000203050480c02c070b41d07030b110040b42640e45071020544200d000d076280c68002c40d40c5071001c948000104041c0c210100101c44844400ba64a003004401d00c420054486240c0000350307900303201c1c03a00660242000095140b095084249007010303e0406009010341848003214542d5044100c07980042d4004410300e90b44c4911080c1032820400c40049503042c05403a0751140c01961005c06801c0300b46905101e01b4402ca228001603900c1000030034041d41100c420450607003c90259907419070114005015640050107010050095101d503410808130280c00001f8014003030007a000c810302034801100210b1079800c090b50742c4011401c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 422460908 1250 422459658 422459671
    0x115050406050a0e0f040906020306031501120f080d0c050304051501230609041407080604090b070c030905270f0c03040b0408040510121802091f09060e010e010603050c03 75
    0xa1113801940a1740b640400c10400210242092082140518010000e074000b158080d0080c03003404502090703210340c920514100c4140f604040148000c07512460501804811b0564140504014030164500d49104101c00f4180c50346d0354585070b003040d15100381001d203804a0301c60100e803144018051210700700d0016420120580c413440c443e181410200d500748c007400444d140d01c1440e0102c0e04100101c40039049100302c1d00e030313a41c000d00b90b0f8491040001b2115100c1e0050070240c0180002140140039006920b1824060705190130803e5540000503100f8004140441c070001c0c015840039024141100b000e0f4102009244441c0c45203400702510603070740402000500000c900501240a2103000d50444010b4080601030031210942e82e03030043c00c0755215201c01c0002030702e494110141c01d1001040002c0e556070041803841310b43c80c4c050018640d4a410031440c2c00014500c0d0340081e240170207124440091488924000143d07250000280440f24141d000303400f414113000c02c001c040404842141c1d48031703c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 422462158 1250 422460908 422460917
    0xe09010e1303090302090a060f0e04080d0231080709020f1e0705010c0504030b010806060f10030b0901080a0506100f0e2706010f060509010801050d02010c08070b0115050406050a 78
    0x1040c00c040f5105441035102030b40058038030043c049803c0c0303e50008002c3c0c444007200c1003000b559a030000d0a440c10101d0f001f070811003080c011809140190f400030080b04070460584030a00369140810310783c43c0140704483d034104c80d0428041100403018440318005003401c01d1b0443c1410354800e4550540d00c500c5054117143c10f404008909142202e03003c0c2c070851a044002088080c40344e000280082d4814003080d2420080711000084214001401d6485000060030039400c0e60700000c04c2c0a594281e02003088141500d98100c25807a84030303106128001c003030400003001c03050b4190600701e0a21201078000010340080100038491400e0300c01a03601255589410b80c10745550321078183c500e04510003a050040a0341e070480260071140015614140c0341441000c1a0781546c46005a407140704907046c090100302c081e40104203504c3c060a50700075141c0181848600306490b6038500d9203c0e80100c5040350310020309001840b000c00003a200303014280c41801e2480c40c0c1070038400094205e0150501000400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 422463408 1250 422462158 422462191
    0x203070b0c090a0e01081b0f031b030c22140c0307080c12041209061817100219090608010608040b1302120d031a060415020a080a0f0e09010e 62
    0x58849108600c010265548401110350f121a606c6884401004803502002c2c180c00000480b490031080c00c003042c0800030300502d02c500b04040d1030484514848125540740c02644200c000a403a51840b001c980071404447c10030600e40302d460041101c040191064545035003004010142801c0030403650801c9550403d80125a01c0c1010300006108110001455502c00e1052004000102d0b0030301c4070190480d01d404c100c44c1c0d110340086800320885e0310400c0020700302c1041000041c4d0b038881c0d0910080141d5094030014a0310000325016a4480c1c10038440d0a180c4115401c01c6e56880b2207050080d10103490000000d5142c808000c06411002c1c0001e01034094040200b0302e0b00469103d0b440701c681d406081c008100d100c8400540e1612500c020903000300b0b00708084100b50344103284840c01d80000080c40716041c2810601e080007130140c0c0d00c49000540c400ca001c16808100030340060440210942c0c0c46680607202c504c0c0042c40d21503001d5001d801503441d03400502250500e485019800030f0494002c1008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 422464658 1250 422463408 422463427
    0x20a05130e070605071406101403030c010207031107060c05120c01180b010f1a07060c02070b0c0115120c0510170405010b01020d0516020103090c090c0c020306070203070b0c 76
    0x80101d0155100103210340c02d000102e0b150030101500d01540612101440c1c0c921501620b07803110400c407000d40f1003440c00f0000f48025420000700703003603002e1701030200c9040804122202c0c2c2264020141603001c03443d041801c0e83c441c030040013640c0107880c217864a802c5d00c0e891642c07075a641d00151042c0e04025500030414040e003071400d501000e402412004c4038411194030b418030319031020003030142e00d86890810b50081034070403440c0009003e01800c200300c145000c0940d2586801030585810000c114010800009000c0ca041c1014102d100d0407907000044001031031105440b0450343e6030190100080c00101c02000c5000d925040007194400d072004038524038444003c4404000801c0c0c0085805103003803d100c24028150700003082004281c080b661481c41001081d140c60042e5095005d07103141c02c0c9c3c1540c005502c41c0c2c00000a4a1180d91721141c030342c0c1c4400901e4160780794050410b0008940004c01d0b025840c0802003a038001c004d48c0065844c03c0145d44801440d004010302584081c040020350300d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 422465908 1250 422464658 422464661
    0x30106060c03050f0d0b0d030c02040c030c021903020c0d06151202010e0f2224030804030311100c0305070201050f01360c09030c0503161202041b0c150504020a0513 72
    0x480c40010b11103e031f04001407401800a0b00c100b0700c20382c0070358a08000c41581c91b000b07208510030910345e40c0041c1b01102c0c0c402c40803121013010b01d604400b1030081010b80512030b01e844040c0d664942c4a10008200601070b103a1001c0c031080346a1007415120004010400940d8200040080942040c0d0b0350058500a510110f001030b40325183d40b120002c62503000700c41c0344050703500c0261160b84903004680e5188400140150302c00d414080a0040c0300100720810020303000300b90b03400440e5880803d0340d0003814400084021685c00c0740620b80400c0d112800c220f440b550a00c0307200d622107201e091781a91941070061212000f580b0048400300e10008100711403606a14401e92003100407078920038000e0000c1d00300018a450080e100854030301800c0c2c03502181070710b0042080e54076440d84613410903070185014001c08092900400030b0b41c2041d503500a010540100d0380950b14510455210400410413130f00d000e0b02d51860040c65100000d19183c144030050381d03101d90b40001c940007190b1f154851302003503c0c1e860 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 422467158 1250 422465908 422465921
    0xf050d050c0a060c290705030a091b080613080a0c0614100302030d0e010c02090402060c121329130b03040524360708010506030106060c03050f0d 64
    0x3640016100b1002031050b6110446038501031180d4441120881089034461241e2692410b4002003901d050010750180d1003100550350000301d6040100380042c2c5616040003810350005440383d0264900310501c5000307030802507160032042e51900c801860225494054840c024965140100038005801205000c206d030440380d50034030480c42c4801207080c00c2006041d03d00c040d10080740640141062015806c0c080e46503848000b0043e1110022049140d00700070550b5401401242c0c808000c0c844121010310400c4102002038051001c0303a503803c141d0a020540c80d50319032108070380c0c440081c0b10221003080001a5500003100d006c1036512000e41c0001444086219004501120000300400040c0100040c1e00c034050110802c2400e415610030b0429414840c046414002080351039940000301c8400010070204505410514400000c0c500050703414040140c0c04000103a464405004061030b081c401c520083c145810000708002041d50b002d80203014903400000c041308003248480c00000540c0210 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 422468408 1250 422467158 422467183
    0x120305180f0d060f0605220e06071706040603080d05010f0803040501090b09030309060a0504090b120c0114190e032b0c02010c02180a0f0216081614030403030f05040f050d05 76
    0x780071002c2c0c0b00200b020003101d1800c407c1a041d04010042c0a1345a010a28070b0041f413aa9442c0d03900f1040e0442d61003500c00003d03003003d4105940d250004082a445806010003113000080468654034042220004041607004050550005c01c01000306070b030031180010441d0317010a00603803151920000641540030f40301d20650031440002c0d6600703485034440e0091080c0c640181301003004480540c203010240c0d07100420000d0780d90001440d0340156004040c0035602880d00407410b440c00e408890800c00000c40d14003000b010442c0041090712030f00d400d020150502034a00146403403824a840e07210703c80c031440045074091041c0301000c1406c0d03900c00c100140c1e0302c43c1c01070074510b514110114042c1b207001003160b000803210324090003103000446600844009400d100d03000c000000040d103c00e0720b16030002115210b10b20215146100180f6500c480c0c0c0c2003004c207800034549031440c508001d400115889200c1c0104101000305122005c1040003400c161041030710404e45100c00c0d4a041c030303c0d0461320180d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 422469658 1250 422468408 422468419
    0xc0537270b09010e04120207031502130f150201050603121b10021c0513030503010b0901090f0f03050f010606080f0405011d0105090c0a0506090d0507120305180f0d060f0605 76
    0x210700320074002601c1c1c0c0aa0700c2042a5045990b0074041240c40b0410381c00010160ac003032080f9071001c209141c01030030070300124910400516558650341c0d550b41c80190310030b5011031845410509440d03020b101d81d0741d0152054024000840c156421001d140c0304552803110410f1000510b650803010800049440e20042d482c110344e00c0c0c010540d110316220146006186250800d0001401c04403503280d440c00541e8981c40301030840c0d0901040c1051350300003128007030404c80c0e00b120001e8100940d8601038001e094100d60003040b1420b50400d1410301e4030ba1600c002c420b0f81420420452140d020300b9a0350f1103010090b0301c0000c4d40310780c9800c5005d4801c503011a80d08081e02c850100c0101410b500880c02104403004481d8840e400c80d0602c41c1c035034028480d80398001c0c42407240e0905030074104980c0c6095840782c0306541c1c03c251a40d20703180d0a8400880c095000590101c0c002d403441d442d40c50b41c564980011200340d21005940c0e00081c050a4070442c0060040da00e030741e440c808028241e04601d0103400024034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 422470908 1250 422469658 422469661
    0x9080d0e070e0610080705030a0b0406030c0303080c04030c14062808010501020f070e040314030a150506090603160e041a0a06030507050a0c0c0537270b09 68
    0x40d8503949085078003604520211140103da039600d0000340c0910303a4440e644601000d41d5450b201a5601c0d08020581c8000e01d0300c500020300d82e507032984180fa020b14800d0b80b85c1c106850940c1002001c0c00701c02021003042201c10001407002c6240117800d0000c44030b01880041c81c46480002242441c02458903075000c100d00070349d41d0620f041c03030342c1e42444a802c55035031040b10aa036a07100490383d0300d6244038081c0041d00010f2040c42001c090071000b582c0203020f800c10b442e8a165100044110380c1c0125a00840070f9941d0b00c600001100401c130120091008a901d40d080c0440ca00002c0c04d40e00c400b0f00031610f80420800c03402009400386550180c5a0300092003045035040c50751164044200c050641c1e0300c5a0f50b075620105d00c0c40d00911449010300c08968881d418505000300c15038400542500903a240208080009610ba940c0d8078003901528038489280e00050b0000380000803209194a2001c020700e8195042c44502c40001c0d1043c401d1005203113200c11202c0003210b0303400038484542840d400820240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 422472158 1250 422470908 422470931
    0xa090b010e060d0c0f030b100c020d14060a11072f09010902041a03090c06030a0f0501141c051b0f04020c06180109080406050d0209040606120f05041509080d 69
    0x203002e1344511100da01c0c0ea1540f051074007400c404a400742c50200754401c03071007407014402a1040c02c0c1900540d01c06045065018581d440b41000038a00000070303600d03603100c034040002d4198075004800109003c000000c4c1060f11540d1a012446400d201e007408030710346498481403040030b143c59640368140140441d1800d50711b44402c00c0107940075004080501c103070700c41c00c20034000b1500116440b0705114000303003160315031100801000f41d10151000c0f42090700d600001c41580460321a0314028461103501e100c5400e40c08090149090301005905180c0412500d510007182001c11940a090390f104000c000c903a4a440011300034a102c0d26099030043d1000c10242d40c8030700001909405410044500c201d401d40c2c11008901766030352044000e284260910080000c43d001d03030068000c00881c440094180701c444030106084031315652081000610a00c4207030b1600c2103074030802004554946040c01a45415218900410000010b840000707649505070801d0207500f1041d901c0c0c03001c40400038040301d203401c2e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 422473408 1250 422472158 422472161
    0xa0609050f12030c0304020f0d05060f01060e030a03080f130506010305030d06051509011b0516060f050c0c0d030504263d06080a0b0108010c0302090a090b010e060d 72
    0x100001c07001d5100d1140540415070b40d400c01e4910034034000312200c1c80c40d0f0b03c1e0380c01e100342c0000390b200705038110310320058080c00a2000c0c0969486074003606401c00c51589812802046403200c503000c603000307801100102000c60b5003d14400c0e4416003160682002c2e894001c0003500032081076a029206008070030003c030401074003100600c50040b1341003060048984401c100424882055070b43c046000040284580650003a00c1c030b9401181c6c00c04035000b04074842e032600f5040c501c3c0702039040c10100d8403800500c13040d5042940310f07803451007914001d420100c0c02010707950b17078002c40c48000b8407403644100e0180400d8402c604603009030046103d00c0340c500740c07205071030131141c000d8203c407808074050204030344698803c40d20b40022040305801e2880007141865080109404070960304801d150319400d02042101041060350030301446441301620542c506804176003101c08010140040600403c4290b28603590804d40c03000703485c1a8500025030341865130043e6142081040c120350449008a80071855421741d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 422474658 1250 422473408 422473423
    0x4050705120903040b0f04080c030718270b072a0201141e04030c1e050609030106030b0702031b0601151110090602040305010c0c0305180a0b0d0b03070e091209030a060905 75
    0x20310b01142c48040d6000c0404d615514103000f0307101141403100003100b440c8255040001181926010910300c0c0c00344101c03485950dc008081940c1a0800350140150300794402c040510f4114407050b034451416043c0340407207110000d51406070400c156019038601e8a01c802d400c0700c5590600071840d03041165251340c0e03503c03141c00922041d202c1c00e00310f0400040d11103400910116002c41c0e2302c038240c0b0351400e01c02001034503002010016015940c6070720100024668808107405110950025505c0c1c800f04040c202031103040f103001035000d8000324010008408601c4001e040c80206003070541010411a0042e840c0c80800011080c00074100300c81d690074071072154010020350b03001d02d0081c0072040340c802c01500d501c1d003c0003005001a0342001904800d242c81185e4030140040104940310700c0ea171726800d44039281c0100341701e40c0d01181e49450030801c81c5000c000c3c54004114503e07240103503140038514640c84030001c1c000c0c04002d9500061900595406210b01910a54403d104000c012294240309907101507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 422475908 1250 422474658 422474669
    0x102150907030c0909080a110c0409030e0a05030115060e0d05060f040b0702030a0f050a020106080304090b0306060a06050a030c170703090c050d020d08160c080f070504050705120903040b0f04 84
    0x11444004aa401e089005171a855070b0458001490f00001000c202c4400940e06801d0303209004459600c00300740c3d114050592001d000380d546041c1d0145034820090041d00d5580124440d0385002c94034048003400c40c4140c0c2c1250305c03e040c0200711450507008154444441100200140100820130101e54601308030f0302c0c0900e000e49850700b0603940c1c0c02c1e4140d94a00c0fa6034a10000304100130304071500a4490341c01440840c010784004a602130f50340c2ca25030300d59045a0001c1c90100d8596111700420300b42004095449601112080e050901d02407010746a0700c0303440110000c040d01d40002007402402608050303104d81903140a01b18900e0803000050060903010400c0b50b40d84010b01e0002203c0ca0170804031120310346c008100d0401c018041c0e560700b03800d90100c051304200900000321100450762407880c2100811120b4013505000c0200c01507d8146541d43d0801e82c4a03a1600d001c1c0010030b584241a81d21807a0b0321b400c80e26032510b03004140c514500850f40071003256000040c001401c8441c8030041c000300c80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 422477158 1250 422475908 422475923
    0x15030e1006080118051b0a081009050f010203071202031302100302090f04150b03091603050f0c1e101103131d01081f0f06060906021504020306070e010215090703 71
    0x1134000007400b5401c040c200140039940010706d1783e440303101300e103040c01460000140100d03141c50791000c806040821540b03c0c809150341d00d440c01e40602100344419082c11015200842c84c510706108040e020f078080342202d034103141c0c0c040000354030500601ea2069050750000d00c005001490203030002d0280d03100c0440701d405091048100b84807420140107000740410302499010401e4148040b40d4200d0f0001051386100d440340046c018441ca003070500d80405903009801514052031400040b44c5810fa9800f810b80c003c141580f10b4030441c40304001c98541541c41180d800214810b00c81c003c0b02e00c080100400040743c00700003168103540b0103c0c2d2544040741c00c03420030700075103050918100c680d2080c00d00c0b80211580041703240c960515180c8405402225041000181148036001050211001c03504403070085038079034400b409000d8041103013980348981d03001115810301e4143d000c2602c60780041c08070800d200c401c10012020b40c4c001d019000c24446042c0c40504a032a1056440d60380301071031f01c01664440e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 422478408 1250 422477158 422477171
    0x1d13081201031401060b031b041e150206010b03040f0201050904060605030a0b01020a0b04061814061008030a140a0c170417060903040509060a0305010231080715030e10060801 77
    0x3110180599006c0302d40da103c805007141c1c0c4d607641c0315203400100c032102140b9800810020800045500350307500317185070f54141001818100a106504c00e0f0300c0d01040015944120010000100c07680c08503680650310140e041604880d41c401030b1858009c80103440d40c014184000420700e560f20901441c03144941d4003040c842001600010780c0c58064924000e00b41d080040d0024000c24a290010403228980c04c1038a1451840e41d254014281d804d4a111481a080744080c01100c115141c806400740082002031751030440b02c80000b400b401c61800e03240c00c04103808140c07040940c2c02544981e0131182c101c0070b00c86054030101f07a0242560320a00070441c5440356142c4e030b1022003800007802c51140c07004000443c1b0345810407040064400300202802c0e031140b07030740c0d03804000184280050045c0801d455500c1d41712045114511100200700d01109481e03102e0001c0822000c90b0018590088500c4519070b070001d050207000480103040f00300e09009461150480c14004040c541d03020b0000c444420b8001c1210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 422479658 1250 422478408 422478443
    0x40e1906090e07031707140a060f140a0e010f0204080f1c05041a04031505060a06020606060f03130210080106081f0611010b040e0d02060c041d1308120103 68
    0x301d44810307041a1581d440b90360180001784180b0b510210f000ca01c00c00c103509040720759440b4030a8440700d042c103000d59044910b0700740400080e4021810340080c038480900240381000050b9150710b90080c1400c0c84c03540c4030742842c000302200394040040100c043d18159a2035440c1c2e07111940d20050442016041d1007038043c04c2d100400341c504040d050f00708035595285021701e0702c0100a00750351950120460303000c0800c4000009000144a0501c8610350180820a85400401c008003829254450380c00e5410040c1082810342da110125003c4650007030342c1c01d44075201e1a111941c9111807600003504230955111180d84540c0000075681210503c0c2d44000701d80d51106915644a10411610381c440e00d1200010710010380107050490031144107400000b0fa00e8404800901034506040400c5e4443e00107a42e642d441c0d0340d041c045180d0050540b508c1c1c0e8545894030115004420501c0c00224075100c140002c00e21021100424002c00c90b00440c003d034642c0c0c500442441c03145405e110490340c041d00107061109 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 422480908 1250 422479658 422479661
    0x1d18040816050601080a173109020a031b0801140613080601030b180705010c120e0d0c0512010b180c0f040b030109050105040e060a051005030609030301051c050d050906040e190609 79
    0x2303240c20400e80041001c0f40e42c98025000e529004030141c0c1020322040c0411240c0b0580b000e03040c1745581e0b0380d001c00c465800d00c44410780c8929940d440c031b08006c42400140405c559088100207101001d0b2001c03913039040581e95400c03038180c0300e80018510b802644000802c0c0710802020500500000059a04a00514801a544100c03500c03480780030442d408181c001040100040030b110745568204040c0c122800e00c00140105103c4104960441d2444d509000390f05221220041c188161002040500c04100001c0c6141c00201d180b600010340200018041d0103d0f8020f840c200c00051140f1600d0b56183c185084035a0030034000c0134041840c080000459141c94020010a2500b000c05010561100300d1048042c1000500501d005403074440009000d40b01041401c0c441c0b07160b44081c40e242d5060004001d114441184468400c1c1a510040b802007000410403000c1c0f00d1180c10210b0340c03850a038002c5000c60180e980822132006100b010401140143c2e000c2c801d0601044904021080e2141c101c0c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 422482014 1106 422480908 422480917
    0x907060912080d09030309021002010203041214030f07090512030705010507030e07090b041415030d03020a050a080603030705030301061d18040816050601080a17 71
    0x10406900240a10140c210000d1064034000c1c1520380c024a4010380048208281d99808200c0815010340d002c0c140345c3d64042d06c109514446000003900075001150140e59008600c100d1000e11445581800346500710a80c843d82541c88218201318170020042540d4144886280007060310341e0341d4100c040414441800039039641c011031070f0050a452001d0300000600d410071851001000d000308039032058460025000843c0e503001300c006405081e01045085280c4546d0080c0900034501e0032082000610544c110b84146460800c201c04074071036a040d00c00010014015150b105100e50b4009411132030040489040400c55111117066500a900200204040f50142c2d0314000040b001c00f010744108448081d05010b010440c0c0c0800f0400a1004051f0031000030000c09213590710503084150f980010840f000340d88c50748811075403400117000c15244200645441a070704180501200c = true := by decide +kernel

theorem cover : BRFrame.Cov 422302158 422482014 := by
  have h0 := BRFrame.cov_init 422302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 422302158 ≤ n) (h2 : n < 422482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
