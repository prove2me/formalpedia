-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.map_defectOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:31.053476+00:00
-- url     : https://prove2.me/submissions/bb9da68c-852a-4c05-badc-e51492254f00

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_substZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_substOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_substTwo
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
theorem _root_.solution (be : MvPowerSeries (ZMod d) F) : map φ (de1 be) = de1 (map φ be) := by
  have hs : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.map φ (MvPowerSeries.subst a be) =
        MvPowerSeries.subst (fun s => MvPowerSeries.map φ (a s)) (MvPowerSeries.map φ be) :=
    fun a ha => MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) be
  unfold de1
  rw [map_sub, map_sub, hs s1 constantCoeff_substOne, hs s0 constantCoeff_substZero, hs s2 constantCoeff_substTwo]
  simp only [map_substOne, map_substZero, map_substTwo]
end Formalism.DworkPowerSeriesWeights.Transfer
