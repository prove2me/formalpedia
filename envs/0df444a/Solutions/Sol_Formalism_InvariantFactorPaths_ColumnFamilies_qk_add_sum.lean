-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:23.492439+00:00
-- url     : https://prove2.me/submissions/93e53ebe-a1f0-42bb-adda-375004a211ce

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
theorem _root_.solution {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) : ∑ a, (qk_add mu s a - mu a) = (s.card : ℤ) := by
  have : ∀ a, qk_add mu s a - mu a = if a ∈ s then 1 else 0 := by
    intro a
    unfold qk_add
    split_ifs <;> ring
  simp only [this]
  simp
end Formalism.InvariantFactorPaths.ColumnFamilies
