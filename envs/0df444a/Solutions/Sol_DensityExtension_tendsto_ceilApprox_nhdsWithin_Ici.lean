-- Prove2me | solution 1 for DensityExtension.tendsto_ceilApprox_nhdsWithin_Ici
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:30:26.37754+00:00
-- url     : https://prove2.me/submissions/14b286f3-ce57-46af-8ca8-c7f396aca437

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Theorems.Thm_DensityExtension_tendsto_ceilApprox
import Theorems.Thm_DensityExtension_ceilApprox_ge

open Filter Topology DensityExtension
open scoped NNReal Topology

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (t : ℝ≥0) :
    Tendsto (ceilApprox t) atTop (𝓝[≥] t) := by
  exact tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_ceilApprox t, Eventually.of_forall fun m => ceilApprox_ge t m⟩
