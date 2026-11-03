-- Prove2me | solution 1 for BFVBound.G_le_geom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:41:17.775338+00:00
-- url     : https://prove2.me/submissions/3ecb8d6d-9765-41b2-a33a-fc1625940bb2

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding

set_option autoImplicit false
open scoped BigOperators

/-!
# Series bounds for the BFV product expectation `F`

Analytic inputs of the quantum max-cut per-edge analyses: the hypergeometric series
`G = 2F1(1/2,1/2;2;.)` and the two-sided bounds on `F s = (8/(3π)) s G(s²)`.
-/

noncomputable section
namespace BFVBound

/-! ## Series bounds for the BFV hypergeometric factor -/

lemma poch_two_pos : ∀ n, 0 < poch 2 n := by
  intro n
  induction n with
  | zero => norm_num [poch]
  | succ n ih => rw [poch]; positivity

lemma poch_half_pos : ∀ n, 0 < poch (1 / 2) n := by
  intro n
  induction n with
  | zero => norm_num [poch]
  | succ n ih => rw [poch]; positivity

lemma poch_half_nonneg (n : ℕ) : 0 ≤ poch (1 / 2) n := (poch_half_pos n).le

lemma factorial_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  exact_mod_cast n.factorial_ne_zero

lemma coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  unfold coeff
  have h := poch_two_pos n
  have h2 := poch_half_nonneg n
  positivity

lemma coeff_zero : coeff 0 = 1 := by simp [coeff, poch]

lemma coeff_one : coeff 1 = 1 / 8 := by
  norm_num [coeff, poch, Nat.factorial]

lemma coeff_succ (n : ℕ) :
    coeff (n + 1) = coeff n * ((n + 1 / 2) ^ 2 / ((n + 2) * (n + 1))) := by
  have h1 : poch (1 / 2) (n + 1) = poch (1 / 2) n * (n + 1 / 2) := by
    rw [poch]; ring
  have h2 : poch 2 (n + 1) = poch 2 n * (n + 2) := by
    rw [poch]; ring
  have hf : (((n + 1).factorial : ℕ) : ℝ) = (n.factorial : ℝ) * ((n : ℝ) + 1) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hp : (poch 2 n : ℝ) ≠ 0 := ne_of_gt (poch_two_pos n)
  have hf' : (n.factorial : ℝ) ≠ 0 := factorial_ne_zero n
  unfold coeff
  rw [h1, h2, hf]
  field_simp

private lemma coeff_le' (n : ℕ) : coeff n ≤ 2 / (((n:ℝ)+1) * ((n:ℝ)+2)) := by
  induction n with
  | zero => rw [coeff_zero]; norm_num
  | succ n ih =>
    have hcoeff : coeff (n+1) =
        coeff n * (((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1))) := by
      rw [coeff_succ]
    rw [hcoeff]
    have hstep : ((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)) ≤ ((n:ℝ)+1) / ((n:ℝ)+3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((n:ℝ) + 1/2)]
    have hA : (0:ℝ) ≤ ((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)) :=
      div_nonneg (sq_nonneg _) (by positivity)
    have hB : (0:ℝ) ≤ 2 / (((n:ℝ)+1) * ((n:ℝ)+2)) := by positivity
    have hprod := mul_le_mul ih hstep hA hB
    have hgoal : (2 / (((n:ℝ)+1) * ((n:ℝ)+2))) * (((n:ℝ)+1) / ((n:ℝ)+3))
        = 2 / ((↑(n+1) + 1) * (↑(n+1) + 2)) := by
      push_cast
      field_simp
      ring
    calc coeff n * (((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)))
        ≤ (2 / (((n:ℝ)+1) * ((n:ℝ)+2))) * (((n:ℝ)+1) / ((n:ℝ)+3)) := hprod
      _ = 2 / ((↑(n+1) + 1) * (↑(n+1) + 2)) := hgoal

lemma coeff_le (n : ℕ) : coeff n ≤ 2 / ((n + 1) * (n + 2)) := coeff_le' n

lemma summable_telescope : Summable (fun n : ℕ => (2:ℝ) / ((n + 1) * (n + 2))) := by
  refine summable_of_sum_range_le (f := fun n : ℕ => (2:ℝ) / ((n + 1) * (n + 2))) (c := 2) (fun n => by positivity) (fun n => ?_)
  have h : (∑ i ∈ Finset.range n, (2:ℝ) / ((i + 1) * (i + 2))) = 2 - 2 / ((n:ℝ) + 1) := by
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; field_simp; ring
  rw [h]
  have hpos : (0:ℝ) ≤ 2 / ((n:ℝ) + 1) := by positivity
  linarith

lemma summable_coeff_mul (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    Summable (fun n : ℕ => coeff n * x ^ n) := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (coeff_nonneg n) (pow_nonneg hx0 n)) (fun n => ?_) summable_telescope
  have h1 : x ^ n ≤ 1 := by
    calc x ^ n ≤ 1 ^ n := pow_le_pow_left₀ hx0 hx1 n
      _ = 1 := one_pow n
  calc coeff n * x ^ n ≤ (2 / ((n+1)*(n+2))) * 1 := by
        apply mul_le_mul (coeff_le n) h1 (by positivity) (by positivity)
    _ = 2 / ((n+1)*(n+2)) := mul_one _

lemma G_ge (x : ℝ) (hx : x ∈ Set.Icc 0 1) : 1 + x / 8 ≤ G x := by
  have hs := summable_coeff_mul x hx
  have h2 : (∑ n ∈ Finset.range 2, coeff n * x ^ n) ≤ G x :=
    hs.sum_le_tsum (Finset.range 2) (fun n _ => mul_nonneg (coeff_nonneg n) (pow_nonneg hx.1 n))
  have hval : (∑ n ∈ Finset.range 2, coeff n * x ^ n) = 1 + x / 8 := by
    simp [Finset.sum_range_succ, coeff_zero, coeff_one]
    ring
  linarith [hval ▸ h2]

lemma c_ge : (0.8488 : ℝ) ≤ 8 / (3 * Real.pi) := by
  rw [le_div_iff₀ (by positivity)]
  have hpi : Real.pi ≤ 3.141593 := le_of_lt (lt_trans Real.pi_lt_d20 (by norm_num))
  nlinarith [Real.pi_gt_three]

lemma c_le : 8 / (3 * Real.pi) ≤ 8 / 9 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.pi_gt_three]

/-- The hypergeometric coefficients are at most `1`. -/
lemma coeff_le_one : ∀ n, coeff n ≤ 1 := by
  intro n
  induction n with
  | zero => rw [coeff_zero]
  | succ n ih =>
    rw [coeff_succ]
    have hnn : (0:ℝ) ≤ coeff n := coeff_nonneg n
    have hratio : ((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg ((n:ℝ) + 1/2)]
    calc coeff n * ((n + 1/2)^2 / ((n + 2) * (n + 1)))
        ≤ 1 * 1 := by
          apply mul_le_mul ih hratio ?_ ?_
          · exact div_nonneg (sq_nonneg _) (by positivity)
          · exact zero_le_one
      _ = 1 := mul_one 1

/-- `G` is dominated by the geometric series: `G x ≤ 1/(1-x)` on `[0,1)`. -/
lemma G_le_geom (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) : G x ≤ 1 / (1 - x) := by
  have hsum : Summable (fun n : ℕ => x ^ n) := summable_geometric_of_lt_one h0 h1
  have hcoef : Summable (fun n : ℕ => coeff n * x ^ n) :=
    summable_coeff_mul x ⟨h0, le_of_lt h1⟩
  have hle : (∑' n, coeff n * x ^ n) ≤ ∑' n, x ^ n := by
    refine Summable.tsum_le_tsum (f := fun n => coeff n * x ^ n) (g := fun n => x ^ n) (fun n => ?_) hcoef hsum
    have hx : (0:ℝ) ≤ x ^ n := pow_nonneg h0 n
    calc coeff n * x ^ n ≤ 1 * x ^ n := mul_le_mul_of_nonneg_right (coeff_le_one n) hx
      _ = x ^ n := one_mul _
  calc G x = ∑' n, coeff n * x ^ n := rfl
    _ ≤ ∑' n, x ^ n := hle
    _ = (1 - x)⁻¹ := tsum_geometric_of_lt_one h0 h1
    _ = 1 / (1 - x) := by rw [one_div]

/-- Upper bound on the product side, positive range: `F s ≤ s` on `[0, 1/3]`. -/
lemma F_le_self (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1 / 3) : F s ≤ s := by
  have hs2 : s ^ 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have hlt : s ^ 2 < 1 := by nlinarith
  have hG := G_le_geom (s ^ 2) (by positivity) hlt
  have hGpos : (0:ℝ) < G (s ^ 2) := lt_of_lt_of_le (by positivity) (G_ge (s ^ 2) hs2)
  have hden : (0:ℝ) < 1 - s ^ 2 := by nlinarith
  have h1m : 1 / (1 - s ^ 2) ≤ 9 / 8 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hc : 8 / (3 * Real.pi) ≤ 8 / 9 := c_le
  have hmain : (8 / (3 * Real.pi)) * G (s ^ 2) ≤ (8 / 9) * (9 / 8) := by
    apply mul_le_mul hc (le_trans hG h1m) hGpos.le (by norm_num)
  calc F s = (8 / (3 * Real.pi)) * s * G (s ^ 2) := rfl
    _ = s * ((8 / (3 * Real.pi)) * G (s ^ 2)) := by ring
    _ ≤ s * ((8 / 9) * (9 / 8)) := by
        apply mul_le_mul_of_nonneg_left _ h0
        simpa using hmain
    _ = s := by ring

/-- Upper bound on the product side, negative range: for `s ∈ [-1, 0]`,
`F s ≤ 0.8488 · s · (1 + s²/8)` (recall `F s < 0` there). -/
lemma F_le_neg (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
    F s ≤ 0.8488 * s * (1 + s ^ 2 / 8) := by
  have hx : s ^ 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have hG := G_ge (s ^ 2) hx
  have hc := c_ge
  have h1 : 0.8488 * (1 + s ^ 2 / 8) ≤ (8 / (3 * Real.pi)) * G (s ^ 2) := by
    have hnn : (0:ℝ) ≤ 1 + s ^ 2 / 8 := by positivity
    calc 0.8488 * (1 + s ^ 2 / 8) ≤ (8 / (3 * Real.pi)) * (1 + s ^ 2 / 8) :=
          mul_le_mul_of_nonneg_right hc hnn
      _ ≤ (8 / (3 * Real.pi)) * G (s ^ 2) := mul_le_mul_of_nonneg_left hG (by positivity)
  calc F s = (8 / (3 * Real.pi)) * s * G (s ^ 2) := rfl
    _ = s * ((8 / (3 * Real.pi)) * G (s ^ 2)) := by ring
    _ ≤ s * (0.8488 * (1 + s ^ 2 / 8)) := mul_le_mul_of_nonpos_left h1 hs0
    _ = 0.8488 * s * (1 + s ^ 2 / 8) := by ring


end BFVBound

open BFVBound


/-- **The series is dominated by the geometric series.** -/
theorem solution (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) : G x ≤ 1 / (1 - x) :=
  G_le_geom x h0 h1

#print axioms solution
