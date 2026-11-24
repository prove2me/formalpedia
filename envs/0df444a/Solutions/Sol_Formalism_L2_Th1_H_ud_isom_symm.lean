-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_isom_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:27:32.954143+00:00
-- url     : https://prove2.me/submissions/8a8d5b62-b642-4eb1-b1f6-9fad6348ba23

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) (x y : V) : H (δ.symm x) (δ.symm y) = H x y := by
  simpa using (h.isom (δ.symm x) (δ.symm y)).symm
end Formalism.L2.Th1.H
