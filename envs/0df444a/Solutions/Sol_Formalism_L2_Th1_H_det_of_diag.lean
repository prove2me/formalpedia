-- Prove2me | solution 1 for Formalism.L2.Th1.H.det_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:08.524826+00:00
-- url     : https://prove2.me/submissions/cc5b187b-7669-4ef0-839c-5ac55b84ce9f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n ℂ V) (l : n → ℂ) (L : V →ₗ[ℂ] V)
    (hL : ∀ i, L (b i) = l i • b i) : LinearMap.det L = ∏ i, l i := by
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b L = Matrix.diagonal l := by
    ext i j
    rw [LinearMap.toMatrix_apply, hL, map_smul, b.repr_self, Finsupp.smul_apply]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, h, h.symm]
  rw [hM, Matrix.det_diagonal]
end Formalism.L2.Th1.H
