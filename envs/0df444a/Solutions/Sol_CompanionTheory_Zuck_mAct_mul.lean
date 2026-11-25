-- Prove2me | solution 1 for CompanionTheory.Zuck.mAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:33.567514+00:00
-- url     : https://prove2.me/submissions/2cc9e43e-13e0-411f-aa9e-ec9fc33966c4

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
theorem _root_.solution {ι ι' ι'' : Type} [Fintype ι] [Fintype ι'] {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) : (mAct (A * B) : (ι → V) →ₗ[ℂ] _) = mAct A ∘ₗ mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [LinearMap.comp_apply, mAct_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm
end CompanionTheory.Zuck
