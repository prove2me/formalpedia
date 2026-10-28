-- Prove2me | solution 2 for AvramDividend.Classical.bv_finite_activity_zero_scale_boundary_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:37:25.968714+00:00
-- url     : https://prove2.me/submissions/d03c9e54-c7d3-42bf-94b8-f8794e517091

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_volterra_origin_package
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_of_local_volterra_derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

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
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  rcases bv_finite_activity_scale_volterra_origin_package
      X hX q hq W hW hBV hFinite with ⟨hW0, G, hWcont, hG, hDer⟩
  refine ⟨hd, hW0, ?_⟩
  have hSlope := derivZeroPlus_of_local_volterra_derivative
    W G X.drift ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift)
    hW0 hWcont hG hDer
  have hdiv :
      (((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift) / X.drift : ℝ) =
      ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift ^ 2 : ℝ) := by
    field_simp [ne_of_gt hd]
    <;> ring
  exact hSlope.trans (congrArg (fun z : ℝ => (z : EReal)) hdiv)
