-- Prove2me | solution 1 for Formalism.L2.Th1.H.norm_expTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:44.01416+00:00
-- url     : https://prove2.me/submissions/3151aa55-a721-49b4-ae85-ca547c6c2357

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
import Theorems.Thm_Formalism_L2_Th1_H_norm_powForm_le

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
theorem _root_.solution {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) :
    ‖expTerm c l n x‖ ≤ ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) := by
  have hn : ‖((n ! : ℕ) : ℂ)‖ = (n ! : ℝ) := by simp
  rw [expTerm, norm_smul, norm_div, hn]
  calc ‖c x‖ / (n ! : ℝ) * ‖powForm (l x) n‖ ≤ ‖c x‖ / (n ! : ℝ) * ‖l x‖ ^ n :=
        mul_le_mul_of_nonneg_left (norm_powForm_le _ _) (by positivity)
    _ = ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) := by ring
end Formalism.L2.Th1.H
