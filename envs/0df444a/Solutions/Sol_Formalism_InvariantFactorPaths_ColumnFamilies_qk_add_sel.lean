-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_add_sel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:23.293919+00:00
-- url     : https://prove2.me/submissions/1222d5f9-44d6-4fe7-b6aa-e06b87c121d9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} {mu nu : Fin n → ℤ} (h : ∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) :
    qk_add mu (univ.filter fun a => nu a = mu a + 1) = nu := by
  funext a
  unfold qk_add
  simp only [mem_filter, mem_univ, true_and]
  split_ifs with h1
  · exact h1.symm
  · have := h a
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
