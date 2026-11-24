-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.unit_weight_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:38.441135+00:00
-- url     : https://prove2.me/submissions/46a879fb-30a7-4001-b5e6-bad00761b0af

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_exponent_transfer
import Theorems.Thm_Formalism_LFunctionChainParameters_UnitWeightPartition_claimHigh_valid
import Theorems.Thm_Formalism_LFunctionChainParameters_UnitWeightPartition_lower_bound_simplified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) (P : ∀ u0, W u0 → PData ι m)
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer
theorem _root_.solution : QuotientSlopeBoundsOfPlaceSums D C Xpp P := by
  intro hH hI hS u0 u
  obtain ⟨hLow, hLow2, hHigh⟩ := hH u0 u
  obtain ⟨hGa, hFo, -⟩ := hI u0 u
  obtain ⟨h4, hB, hsz⟩ := hS
  obtain ⟨hIO, hLT, hRX⟩ := hsz u0 u
  have hEe := exponent_transfer D P hI u0 u
  have lo := UnitWeightPartition.lower_bound_simplified _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLow hLow2
  have hi := UnitWeightPartition.claimHigh_valid _ _ _ _ _ _ _ _ _ _ _ hHigh
  have hIOp : 0 ≤ (P u0 u).IOp := by
    have h1 : UnitWeightPartition.IO (P u0 u).S (P u0 u).l (P u0 u).io = 2 * (P u0 u).IOp := hLow2.2.2.2.2.2.2.1
    have h2 : 0 ≤ UnitWeightPartition.IO (P u0 u).S (P u0 u).l (P u0 u).io :=
      Finset.sum_nonneg fun w hw =>
        mul_nonneg (mul_nonneg (by norm_num) (hLow.1 w hw)) (hLow.2.2.2.2.2.2.2.1 w hw)
    linarith
  rw [hGa, hFo, hEe]
  unfold PData.Ga PData.Fo PData.Ee
  constructor
  · have h0 : 0 ≤ C.cSl1 * (m : ℝ) * D.B0 := by
      rw [mul_assoc]; exact mul_nonneg (by linarith) hB
    linarith
  · unfold Lo5
    have h1 : 4 * (P u0 u).IOp ≤ C.cSl1 * D.IO u0 :=
      calc 4 * (P u0 u).IOp ≤ C.cSl1 * (P u0 u).IOp := mul_le_mul_of_nonneg_right h4 hIOp
        _ ≤ C.cSl1 * D.IO u0 := mul_le_mul_of_nonneg_left hIO (by linarith)
    linarith
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
