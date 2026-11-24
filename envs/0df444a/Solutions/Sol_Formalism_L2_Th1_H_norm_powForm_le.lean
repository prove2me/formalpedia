-- Prove2me | solution 1 for Formalism.L2.Th1.H.norm_powForm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:26.964301+00:00
-- url     : https://prove2.me/submissions/5181d312-4720-426e-81ab-6eb132f74b36

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
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (l : V →L[ℂ] ℂ) (n : ℕ) : ‖powForm l n‖ ≤ ‖l‖ ^ n := by
  calc ‖powForm l n‖ ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ‖ * ∏ _i : Fin n, ‖l‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖l‖ ^ n := by rw [ContinuousMultilinearMap.norm_mkPiAlgebra]; simp
end Formalism.L2.Th1.H
