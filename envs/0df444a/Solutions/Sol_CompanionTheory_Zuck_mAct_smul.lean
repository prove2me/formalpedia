-- Prove2me | solution 1 for CompanionTheory.Zuck.mAct_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:41.171025+00:00
-- url     : https://prove2.me/submissions/573fcdc8-d438-4127-b2a6-3fdd596da4ce

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
theorem _root_.solution {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (a : ℂ) (A : Matrix ι' ι ℂ) :
    (mAct (a • A) : (ι → V) →ₗ[ℂ] _) = a • mAct A := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, LinearMap.smul_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul]
end CompanionTheory.Zuck
