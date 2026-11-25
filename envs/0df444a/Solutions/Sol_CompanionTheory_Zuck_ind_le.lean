-- Prove2me | solution 1 for CompanionTheory.Zuck.ind_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:33.801159+00:00
-- url     : https://prove2.me/submissions/716a70d6-f9b9-4c81-a08f-c4616ddd275e

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)
variable {n : ℕ}
namespace CompanionTheory.Zuck
theorem _root_.solution {m : ℕ} (J : Sub n m) (a : Fin n) : (if a ∈ J.1 then 1 else 0 : ℕ) ≤ m := by
  split_ifs with h
  · rw [← J.2]; exact Finset.card_pos.2 ⟨a, h⟩
  · exact Nat.zero_le _
end CompanionTheory.Zuck
