-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_finite_eventual_nonnegative_lintegral_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:24:08.154664+00:00
-- url     : https://prove2.me/submissions/782f27cb-839c-4dba-be9c-1fb8b69215ac

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Finite-measure eventual L2 control transfers a.e limits to genuine ENNReal means. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (B R : ℝ≥0) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hB : ∀ n, N ≤ n → eLpNorm (Y n) 2 μ ≤ (B : ENNReal))
    (hMass : (μ Set.univ) ^ (1 / 2 : ℝ) ≤ (R : ENNReal))
    (hNonneg : ∀ n ω, 0 ≤ Y n ω)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧ (0 ≤ᵐ[μ] Z) ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂μ)
        atTop (nhds (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)) := by
  obtain ⟨hZ, hMean⟩ :=
    avram_p2_j_ui_finite_measure_eventual_l2_mass_expectations
      μ Y Z B R N hm hB hMass hae
  have hZn : 0 ≤ᵐ[μ] Z := by
    filter_upwards [hae] with ω hω
    exact ge_of_tendsto hω
      (Filter.Eventually.of_forall (fun n => hNonneg n ω))
  have hYShift (n : ℕ) : Integrable (Y (n + N)) μ := by
    have h2 : MemLp (Y (n + N)) 2 μ :=
      ⟨hm (n + N), lt_of_le_of_lt (hB (n + N) (by omega)) (by simp)⟩
    exact memLp_one_iff_integrable.mp (h2.mono_exponent (by norm_num))
  have hMeanShift : Tendsto (fun n : ℕ => ∫ ω, Y (n + N) ω ∂μ)
      atTop (nhds (∫ ω, Z ω ∂μ)) :=
    (Filter.tendsto_add_atTop_iff_nat N).2 hMean
  have hLinShift :=
    avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence
      μ (fun n ω => Y (n + N) ω) Z hYShift hZ
      (fun n => Filter.Eventually.of_forall (hNonneg (n + N)))
      hZn hMeanShift
  exact ⟨hZ, hZn, (Filter.tendsto_add_atTop_iff_nat N).1 hLinShift⟩
