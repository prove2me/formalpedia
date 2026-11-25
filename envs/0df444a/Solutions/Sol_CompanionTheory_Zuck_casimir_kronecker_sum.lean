-- Prove2me | solution 1 for CompanionTheory.Zuck.casimir_kronecker_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:33:57.87611+00:00
-- url     : https://prove2.me/submissions/0092c6ef-3227-47c7-8a95-2c5ecf63d300

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
theorem _root_.solution (n : ℕ) :
    (∑ a : Fin n, ∑ b : Fin n, Matrix.single a b (1 : ℂ) ⊗ₖ (-(Matrix.single b a (1 : ℂ))ᵀ) =
      (-1 : ℂ) • ((cM n)ᵀ * cM n)) ∧
    (∑ a : Fin n, ∑ b : Fin n, (-(Matrix.single a b (1 : ℂ))ᵀ) ⊗ₖ Matrix.single b a (1 : ℂ) =
      (-1 : ℂ) • ((cM n)ᵀ * cM n)) := by
  constructor <;> ext ⟨c, d⟩ ⟨c', d'⟩ <;>
    simp only [Matrix.sum_apply, kroneckerMap_apply, Matrix.neg_apply,
      transpose_apply, Matrix.smul_apply, Matrix.mul_apply, cM, Matrix.single_apply] <;>
    by_cases e1 : c = d <;> by_cases e2 : c' = d' <;> simp [e1, e2, ite_and, eq_comm]
end CompanionTheory.Zuck
