-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_v_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:24.807576+00:00
-- url     : https://prove2.me/submissions/586d175a-ff5d-467c-93d7-5f452f0611b1

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
theorem _root_.solution {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) :
    qk_v (qk_add mu s) = s.piecewise (fun i => qk_v mu i - 1) (qk_v mu) := by
  funext i
  unfold qk_v qk_add
  by_cases hi : i ∈ s
  · simp only [hi, if_true, piecewise_eq_of_mem]
    push_cast
    ring
  · simp only [hi, if_false, piecewise_eq_of_notMem, not_false_eq_true]
end Formalism.InvariantFactorPaths.ColumnFamilies
