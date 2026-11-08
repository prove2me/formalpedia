-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn54_original_BV_truncated_moment_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:10:24.371386+00:00
-- url     : https://prove2.me/submissions/331fab48-e5b5-4b54-9f56-de9dbb7a0978

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (C : ℝ≥0∞) (hC : 0 < C)
    (hDrift : 0 < X.drift) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < C ∧ ε ≤ 1 ∧
      q * ε + (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν) < X.drift := by
  have hint := chat07_bv_negative_jump_min_abs_integrable X hBV
  have hmem :
      ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ∈ Iio (0 : ℝ) :=
    ae_restrict_mem measurableSet_Iio
  have hlim :
      Tendsto
        (fun θ : ℝ => ∫ z in Iio (0 : ℝ), min θ⁻¹ (-z) ∂X.ν)
        atTop (nhds (0 : ℝ)) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (l := (atTop : Filter ℝ))
      (μ := X.ν.restrict (Iio (0 : ℝ)))
      (F := fun (θ : ℝ) (z : ℝ) => min θ⁻¹ (-z))
      (f := fun _ => (0 : ℝ))
      (fun z : ℝ => min 1 |z|) ?_ ?_ hint ?_
    · simpa using h
    · refine Eventually.of_forall (fun θ => ?_)
      exact (measurable_const.min measurable_neg).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with θ hθ
      filter_upwards [hmem] with z hz
      have hp : 0 < θ := lt_of_lt_of_le (by norm_num) hθ
      have hzneg : z < 0 := hz
      have hfnonneg : 0 ≤ min θ⁻¹ (-z) :=
        le_min (le_of_lt (inv_pos.mpr hp)) (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg hfnonneg]
      have hi : θ⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hθ
      simpa [abs_of_neg hzneg] using
        (min_le_min hi (le_refl (-z)))
    · filter_upwards [hmem] with z hz
      have hznonneg : 0 ≤ -z := by change z < (0 : ℝ) at hz; linarith
      have hi : Tendsto (fun θ : ℝ => θ⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero
      simpa [min_eq_left hznonneg] using
        (hi.min (tendsto_const_nhds : Tendsto (fun _ : ℝ => -z) atTop (nhds (-z))))
  have hsum :
      Tendsto
        (fun θ : ℝ => q * θ⁻¹ +
          (∫ z in Iio (0 : ℝ), min θ⁻¹ (-z) ∂X.ν))
        atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_inv_atTop_zero.const_mul q).add hlim
  have hcap :
      Tendsto (fun θ : ℝ => ENNReal.ofReal θ⁻¹)
        atTop (nhds (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
        (tendsto_inv_atTop_zero : Tendsto (fun θ : ℝ => θ⁻¹) atTop (nhds 0))
  have hev : ∀ᶠ θ : ℝ in atTop,
      q * θ⁻¹ + (∫ z in Iio (0 : ℝ), min θ⁻¹ (-z) ∂X.ν) <
        X.drift :=
    hsum.eventually (isOpen_Iio.mem_nhds hDrift)
  have hcev : ∀ᶠ θ : ℝ in atTop, ENNReal.ofReal θ⁻¹ < C :=
    hcap.eventually (isOpen_Iio.mem_nhds hC)
  obtain ⟨θ, hθ⟩ :=
    (hev.and (hcev.and (eventually_ge_atTop (1 : ℝ)))).exists
  refine ⟨θ⁻¹, inv_pos.mpr (lt_of_lt_of_le (by norm_num) hθ.2.2),
    hθ.2.1, inv_le_one_of_one_le₀ hθ.2.2, ?_⟩
  simpa using hθ.1
