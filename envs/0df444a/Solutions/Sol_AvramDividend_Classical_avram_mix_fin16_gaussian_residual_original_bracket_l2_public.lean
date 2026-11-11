-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_bracket_l2_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:28:07.68513+00:00
-- url     : https://prove2.me/submissions/12c9ef90-7294-46a1-9afc-ddbd0f951fc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise22_original_gaussian_cutoff_exact_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_anoise23_original_residual_square_integrable_of_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_anoise24_original_cutoff_square_expectations_converge
import Theorems.Thm_AvramDividend_Classical_avram_anoise25_original_nearzero_gaussian_variance_integral_bound
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Original-process cutoff moments, uniformly controlled tail, and source limit give the exact Gaussian residual bracket. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t
  have hSource : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
      atTop (nhds (R t ω)) := by
    filter_upwards [hRsource] with ω hω
    exact hω t
  have hCutMeas (n : ℕ) : AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P := by
    exact ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  have hRMeas : AEStronglyMeasurable (R t) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hCutMeas hSource
  have hCut0 := (avram_anoise22_original_gaussian_cutoff_exact_second_moment
    X hX hFinite 0 t).1
  have hInt := avram_anoise23_original_residual_square_integrable_of_cutoff
    X hFinite R t hSource hRMeas hCutMeas hCut0
  have hConv := avram_anoise24_original_cutoff_square_expectations_converge
    X hFinite R t hSource hCutMeas hCut0
  let V : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  have hTail (n : ℕ) : 0 ≤
      (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) ∧
      (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) ≤
        (1 / ((n : ℝ) + 1)) ^ 2 * V := by
    simpa [V] using
      (avram_anoise25_original_nearzero_gaussian_variance_integral_bound X hFinite n)
  have hEps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hUpper : Tendsto
      (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2 * V)
      atTop (nhds 0) := by
    simpa using (hEps.pow 2).mul_const V
  have hTailLim : Tendsto
      (fun n : ℕ => ∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)
      atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hUpper (fun n => (hTail n).1) (fun n => (hTail n).2)
  have hFormulaLim : Tendsto
      (fun n : ℕ => (t : ℝ) * X.σ ^ 2 +
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν))
      atTop (nhds ((t : ℝ) * X.σ ^ 2)) := by
    simpa using (tendsto_const_nhds
      (x := (t : ℝ) * X.σ ^ 2)).add (hTailLim.const_mul (t : ℝ))
  have hConFormula : Tendsto
      (fun n : ℕ => (t : ℝ) * X.σ ^ 2 +
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν))
      atTop (nhds (∫ ω, (R t ω) ^ 2 ∂P)) := by
    convert hConv using 1
    ext n
    exact (avram_anoise22_original_gaussian_cutoff_exact_second_moment
      X hX hFinite n t).2.symm
  exact ⟨hInt, tendsto_nhds_unique hConFormula hFormulaLim⟩
