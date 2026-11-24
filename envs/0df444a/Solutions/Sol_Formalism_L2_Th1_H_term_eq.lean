-- Prove2me | solution 1 for Formalism.L2.Th1.H.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:27:30.063853+00:00
-- url     : https://prove2.me/submissions/913dc0fa-3090-4fb8-b953-9d0c2cbb2121

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
theorem _root_.solution (H : Sesq V) (α : V → ℂ) (w x z : V) :
    α x * opU H x (kerK H w) z = kC H α w x * Complex.exp (kL H w x z) := by
  simp only [opU, kerK, kC, kL, ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
    LinearMap.flip_apply, smul_eq_mul, map_add, map_sub, LinearMap.add_apply]
  rw [mul_assoc]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [ContinuousLinearMap.sub_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.flip_apply]
  ring
end Formalism.L2.Th1.H
