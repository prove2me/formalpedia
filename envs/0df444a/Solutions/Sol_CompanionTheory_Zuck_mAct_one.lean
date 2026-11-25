-- Prove2me | solution 1 for CompanionTheory.Zuck.mAct_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:37:15.507297+00:00
-- url     : https://prove2.me/submissions/52d91e0b-7b64-42fd-9aa2-eb179ad6ebb9

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Theorems.Thm_CompanionTheory_Zuck_mAct_apply

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
variable {k r : ℕ}
namespace CompanionTheory.Zuck
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] :
    (mAct (1 : Matrix ι ι ℂ) : (ι → V) →ₗ[ℂ] _) = LinearMap.id := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct_apply, Matrix.one_apply]
end CompanionTheory.Zuck
