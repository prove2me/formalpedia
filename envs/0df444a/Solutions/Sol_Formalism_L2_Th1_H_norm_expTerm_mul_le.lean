-- Prove2me | solution 1 for Formalism.L2.Th1.H.norm_expTerm_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:00:11.854218+00:00
-- url     : https://prove2.me/submissions/ca041bb7-a57a-4005-9853-235160ddb195

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
import Theorems.Thm_Formalism_L2_Th1_H_norm_expTerm_le

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
theorem _root_.solution {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) (r : ℝ)
    (hr : 0 ≤ r) : ‖expTerm c l n x‖ * r ^ n ≤ ‖c x‖ * Real.exp (r * ‖l x‖) := by
  calc ‖expTerm c l n x‖ * r ^ n ≤ ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) * r ^ n :=
        mul_le_mul_of_nonneg_right (norm_expTerm_le c l n x) (pow_nonneg hr n)
    _ = ‖c x‖ * ((r * ‖l x‖) ^ n / (n ! : ℝ)) := by ring
    _ ≤ ‖c x‖ * Real.exp (r * ‖l x‖) :=
        mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (by positivity) n) (norm_nonneg _)
end Formalism.L2.Th1.H
