-- Prove2me | solution 1 for CompanionTheory.Zuck.cM_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:33.790673+00:00
-- url     : https://prove2.me/submissions/92b6b4ea-0882-4ea3-960c-4a60f3fed8aa

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne

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
theorem _root_.solution {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Aᵀ * B = 1) :
    cM n * (A ⊗ₖ B) = (1 : Matrix Unit Unit ℂ) * cM n := by
  rw [Matrix.one_mul]
  ext _ ⟨c, d⟩
  have := congrFun (congrFun h c) d
  simp only [Matrix.mul_apply, Matrix.one_apply, transpose_apply] at this
  simp only [Matrix.mul_apply, cM, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, kroneckerMap_apply, this]
end CompanionTheory.Zuck
