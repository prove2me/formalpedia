-- Prove2me | solution 1 for Formalism.L2.Th1.H.summable_norm_expTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:37.882056+00:00
-- url     : https://prove2.me/submissions/e1af0692-6cf4-4ef1-b9b1-122345eb3f42

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
import Theorems.Thm_Formalism_L2_Th1_H_norm_expTerm_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ)
    (h : ∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖l x‖)) (n : ℕ) :
    Summable fun x => ‖expTerm c l n x‖ := by
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (h 1)
  have := norm_expTerm_mul_le c l n x 1 zero_le_one
  simpa using this
end Formalism.L2.Th1.H
