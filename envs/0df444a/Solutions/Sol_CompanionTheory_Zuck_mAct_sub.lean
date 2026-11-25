-- Prove2me | solution 1 for CompanionTheory.Zuck.mAct_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:37:25.196134+00:00
-- url     : https://prove2.me/submissions/178dff11-9cc4-48ef-8539-a08a79b3f86f

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
theorem _root_.solution {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Matrix ι' ι ℂ) :
    (mAct (A - B) : (ι → V) →ₗ[ℂ] _) = mAct A - mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, LinearMap.sub_apply, Pi.sub_apply, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
end CompanionTheory.Zuck
