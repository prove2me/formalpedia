-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:23.96415+00:00
-- url     : https://prove2.me/submissions/f6e1ed14-8609-404a-bf6e-47b4aea237ce

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K ι κ : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {α : Type*} (s : Finset α) (N : α → ι →₀ ℕ)
    (W : α → MvPolynomial κ (MvPolynomial ι K)) (h : ∀ a ∈ s, BiLe (N a) (W a)) :
    BiLe (∑ a ∈ s, N a) (∏ a ∈ s, W a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact biLe_one
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact biLe_mul (h a (Finset.mem_insert_self a s))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))
end Formalism.InvariantFactorPaths.G7
