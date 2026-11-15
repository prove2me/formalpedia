-- Prove2me | solution 1 for AvramDividend.Classical.avram_a31_original_gaussian_source_ae_representative_measurable_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:46:06.795927+00:00
-- url     : https://prove2.me/submissions/f4e9ef16-8cdc-4f77-932f-118172d3b335

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Any pointwise a.e. representative of the original intrinsic Gaussian limit is a.e. measurable at each physical time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ t : ℝ≥0, AEMeasurable (G t) P := by
  obtain ⟨H, hAdapt, _, hHEq⟩ :=
    avram_a24_original_gaussian_adapted_zero_origin_20261113 X R hR
  intro t
  have hMH : Measurable (H t) :=
    (hAdapt t).mono (𝓕.le t) le_rfl
  have hAE : (H t) =ᵐ[P] (G t) := by
    filter_upwards [hHEq, hEq] with ω hHω hGω
    calc
      H t ω = R t ω := hHω t
      _ = G t ω := (hGω t).symm
  exact hMH.aemeasurable.congr hAE
