-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_canonical_residual_zero_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:48:10.698255+00:00
-- url     : https://prove2.me/submissions/044dd982-1da3-41ff-84fe-edf450522119

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The canonical actual-source BV residual has initial value zero:
there are no original positive-time downward jumps in (0,0]. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ((0 : ℝ) * X.drift - X.X 0 ω) -
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ (0 : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal = 0 := by
  have hpoint (u : ℝ≥0) : ¬ (0 < u ∧ u = (0 : ℝ≥0)) := by
    intro h
    exact (ne_of_gt h.1) h.2
  simp [X.X_zero ω, hpoint]
