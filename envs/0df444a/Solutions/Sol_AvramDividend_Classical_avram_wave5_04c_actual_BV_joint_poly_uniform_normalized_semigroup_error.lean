-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_BV_joint_poly_uniform_normalized_semigroup_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:59:01.809461+00:00
-- url     : https://prove2.me/submissions/2f02d1ea-1196-48aa-bef2-89d664b7ccb3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Uniform right-time original-source C1 semigroup polynomial
approximation for the SAME Q that also approximates original Levy jumps. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      (∀ y : ℝ, y < 0 →
        |Polynomial.eval (Real.exp y) Q - (w x - w (x + y))| ≤
          η * (1 - Real.exp y) +
            (if y < -M then 2 * |w x - w (x + y)| else 0)) ∧
      ∀ h : ℝ≥0, 0 < h → h ≤ (1 / 2 : ℝ≥0) →
        |(h : ℝ)⁻¹ * (∫ ω,
          (w x - w (x - ((h : ℝ) * X.drift - X.X h ω))) -
          Polynomial.eval
            (Real.exp (-((h : ℝ) * X.drift - X.X h ω))) Q ∂P)| ≤
        η * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) + 2 * L) := by
  have htail :=
    avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
      X hX hBV η hη
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htail
  have hM : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  obtain ⟨Q, hQ, hR, hJump⟩ :=
    avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
      w hw x (N : ℝ) η hM hη
  refine ⟨N, hM, Q, hQ, hJump, ?_⟩
  have hPoint (r : ℝ) (hr : 0 ≤ r) :
      |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
        η * (1 - Real.exp (-r)) +
          (if (N : ℝ) < r then 2 * L * r else 0) := by
    have hh := hR r hr
    have hLipR : |w x - w (x - r)| ≤ L * r := by
      have hk := hLip x (x - r)
      have hdif : |x - (x - r)| = r := by
        have heq : x - (x - r) = r := by ring
        rw [heq, abs_of_nonneg hr]
      simpa only [hdif] using hk
    by_cases hm : (N : ℝ) < r
    · simp only [if_pos hm] at hh ⊢
      nlinarith
    · simpa [hm] using hh
  intro h hhpos hhhalf
  have hbase :=
    avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
      X hX hBV w hw L hL x (N : ℝ) η hη.le Q hPoint
      h (by exact le_trans hhhalf (by norm_num))
  have hm :=
    avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
      X hX hBV h hhpos hhhalf
  have ht := hN N le_rfl h hhpos hhhalf
  have hi : 0 ≤ (h : ℝ)⁻¹ :=
    inv_nonneg.mpr (NNReal.coe_nonneg h)
  have hc : 0 ≤ 2 * L := by linarith
  calc
    |(h : ℝ)⁻¹ * (∫ ω,
      (w x - w (x - ((h : ℝ) * X.drift - X.X h ω))) -
        Polynomial.eval (Real.exp (-((h : ℝ) * X.drift - X.X h ω))) Q ∂P)| =
      (h : ℝ)⁻¹ * |∫ ω,
      (w x - w (x - ((h : ℝ) * X.drift - X.X h ω))) -
        Polynomial.eval (Real.exp (-((h : ℝ) * X.drift - X.X h ω))) Q ∂P| := by
          rw [abs_mul, abs_of_nonneg hi]
    _ ≤ (h : ℝ)⁻¹ * (
      η * (∫ ω, (h : ℝ) * X.drift - X.X h ω ∂P) +
      2 * L * (∫ ω,
        if (N : ℝ) < (h : ℝ) * X.drift - X.X h ω
        then (h : ℝ) * X.drift - X.X h ω else 0 ∂P)) :=
          mul_le_mul_of_nonneg_left hbase hi
    _ = η * ((h : ℝ)⁻¹ *
      (∫ ω, (h : ℝ) * X.drift - X.X h ω ∂P)) +
      2 * L * ((h : ℝ)⁻¹ *
      (∫ ω, if (N : ℝ) < (h : ℝ) * X.drift - X.X h ω
        then (h : ℝ) * X.drift - X.X h ω else 0 ∂P)) := by ring
    _ ≤ η * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P)) +
      2 * L * η :=
        add_le_add
          (mul_le_mul_of_nonneg_left hm hη.le)
          (mul_le_mul_of_nonneg_left (le_of_lt ht) hc)
    _ = η * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) + 2 * L) := by ring
