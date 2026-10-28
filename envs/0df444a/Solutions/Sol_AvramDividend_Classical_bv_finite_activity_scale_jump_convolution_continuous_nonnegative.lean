-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_scale_jump_convolution_continuous_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:11:49.329435+00:00
-- url     : https://prove2.me/submissions/d1eb1e83-61a0-4089-aa97-e727a720d719

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_positive
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_bv_jump_convolution_at_zero_eq_zero
import Mathlib.Topology.Order.LeftRight
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Combine the right limit, endpoint value and interior continuity of the jump convolution. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)
      (Ici (0 : ℝ)) := by
  let G : ℝ → ℝ := fun x => ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν
  have hpositive : ContinuousOn G (Ioi (0 : ℝ)) := by
    exact bv_finite_activity_scale_jump_convolution_continuous_positive
      X hX q hq W hW hBV hFinite
  have hzero : G 0 = 0 := by
    simpa only [G, zero_add] using bv_jump_convolution_at_zero_eq_zero X q W hW
  have hlim : Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
    bv_finite_activity_scale_jump_convolution_tendsto_zero X hX q hq W hW hBV hFinite
  have hright : ContinuousWithinAt G (Ici (0 : ℝ)) 0 := by
    apply continuousWithinAt_Ioi_iff_Ici.mp
    change Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (G 0))
    simpa only [hzero] using hlim
  intro x hx
  by_cases h0 : x = 0
  · subst x
    exact hright
  · have hxpos : 0 < x := by
      rcases eq_or_lt_of_le (mem_Ici.mp hx) with h | h
      · exact False.elim (h0 h.symm)
      · exact h
    exact (hpositive.continuousAt (isOpen_Ioi.mem_nhds hxpos)).continuousWithinAt
