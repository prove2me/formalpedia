-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_limit_field_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:32:55.825199+00:00
-- url     : https://prove2.me/submissions/09b7722d-cbca-4293-b9fc-4e74c3d2bffa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_cauchy_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite negative jump activity constructs a simultaneous pathwise limit
of the original physical compensated cutoffs on the same probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        Tendsto
          (fun n : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω)
          atTop (𝓝 (G T ω)) := by
  classical
  let f (T : ℝ≥0) (ω : Ω) (n : ℕ) : ℝ :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω
  let G (T : ℝ≥0) (ω : Ω) : ℝ :=
    if h : CauchySeq (f T ω) then
      Classical.choose (cauchySeq_tendsto_of_complete h)
    else 0
  refine ⟨G, ?_⟩
  filter_upwards
      [avram_ubv_mixed13_original_finite_activity_physical_residual_cauchy_ae
        X hFinite] with ω hω
  intro T
  have hc : CauchySeq (f T ω) := hω T
  change Tendsto (f T ω) atTop
    (𝓝 (if h : CauchySeq (f T ω) then
      Classical.choose (cauchySeq_tendsto_of_complete h) else 0))
  rw [dif_pos hc]
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete hc)
