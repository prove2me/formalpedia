-- Prove2me | solution 1 for Formalism.L2.Th1.H.exists_form_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:11.412006+00:00
-- url     : https://prove2.me/submissions/a89fed56-2260-495c-9aca-31f7ca232557

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (H : Sesq V) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, ‖LinearMap.toContinuousLinearMap (H.flip u)‖ ≤ K * ‖u‖ := by
  let T : V →L[ℝ] (V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap (flipR H)
  exact ⟨‖T‖, norm_nonneg _, fun u => T.le_opNorm u⟩
end Formalism.L2.Th1.H
