-- Prove2me | solution 3 for AvramDividend.Classical.bv_finite_activity_zero_scale_boundary_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:44:07.591456+00:00
-- url     : https://prove2.me/submissions/f88dff8b-49a9-4505-8cf2-b36a3d116422

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_volterra_origin_package
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_of_local_volterra_derivative
import Mathlib.Topology.Algebra.Order.Field

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Finite-activity Volterra renewal data determine both scale boundary values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    0 < X.drift ∧ W 0 = 1 / X.drift ∧
      derivZeroPlus W =
        (((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift ^ 2 : ℝ) : EReal) := by
  have hD : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  obtain ⟨hW0, G, hWcont, hG, hDer⟩ :=
    bv_finite_activity_scale_volterra_origin_package
      X hX q hq W hW hBV hFinite
  refine ⟨hD, hW0, ?_⟩
  have hlim :=
    derivZeroPlus_of_local_volterra_derivative
      W G X.drift ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift)
      hW0 hWcont hG hDer
  have hAlg :
      ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift) / X.drift =
      (q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift ^ 2 := by
    field_simp [ne_of_gt hD]
  exact hlim.trans (congrArg (fun z : ℝ => (z : EReal)) hAlg)
