-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_original_rightcont_predictable_total_occupation_gridfree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:23:27.330589+00:00
-- url     : https://prove2.me/submissions/401edce3-37b3-43f6-9f05-df45ea00862e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_positive_horizon_fine_source_grid_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_rightcont_source_predictable_total_occupation_levy_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K) :
    M (((Ioc 0 T) ×ˢ (Set.univ : Set Ω)) ×ˢ (Set.univ : Set ℝ)) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  obtain ⟨grid, hGrid, hMesh, hBound⟩ :=
    avram_wave6_01_positive_horizon_fine_source_grid_witness T hT
  exact avram_wave5_01_bv_actual_rightcont_source_predictable_total_occupation_levy_rate
    X hBV hFinite T hT grid hGrid hMesh hBound K hK M hM
