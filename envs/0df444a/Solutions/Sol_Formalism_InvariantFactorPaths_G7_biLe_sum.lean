-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:45:56.536884+00:00
-- url     : https://prove2.me/submissions/e321efa4-4bf7-4229-92b3-e0912fc9284c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_add

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
theorem _root_.solution {α : Type*} {n0 : ι →₀ ℕ} (s : Finset α)
    (W : α → MvPolynomial κ (MvPolynomial ι K)) (h : ∀ a ∈ s, BiLe n0 (W a)) :
    BiLe n0 (∑ a ∈ s, W a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact biLe_zero n0
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact biLe_add (h a (Finset.mem_insert_self a s))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))
end Formalism.InvariantFactorPaths.G7
