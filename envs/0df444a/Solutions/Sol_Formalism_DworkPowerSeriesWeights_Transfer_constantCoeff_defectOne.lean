-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_defectOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:41.555327+00:00
-- url     : https://prove2.me/submissions/92d3b1f3-d98b-48ac-ac45-6f0108116f1f

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.DworkPowerSeriesWeights.Transfer
variable {F K : Type} [Field F] [Field K] (φ : F →+* K) {d : ℕ}
variable [NeZero d]
namespace Formalism.DworkPowerSeriesWeights.Transfer
theorem _root_.solution {be : MvPowerSeries (ZMod d) F} (h : constantCoeff be = 0) :
    constantCoeff (de1 be) = 0 := by
  have hz : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a be) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha h
  unfold de1
  rw [map_sub, map_sub, hz s1 constantCoeff_substOne, hz s0 constantCoeff_substZero, hz s2 constantCoeff_substTwo]
  simp
end Formalism.DworkPowerSeriesWeights.Transfer
