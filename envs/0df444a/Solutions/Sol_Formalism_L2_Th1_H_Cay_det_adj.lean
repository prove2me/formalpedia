-- Prove2me | solution 1 for Formalism.L2.Th1.H.Cay.det_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:03.925169+00:00
-- url     : https://prove2.me/submissions/39f4ac70-8d50-46bd-a469-86ddca1d5dc2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_UnitaryEighthOf
import Theorems.Thm_Formalism_L2_Th1_H_Cay_gram_det_ne_zero

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
open Formalism.L2.Th1.H.Cay
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.Th1.H.Cay
theorem _root_.solution (H : Sesq V) (hpos : IsPosDef H) (f f' : V →ₗ[ℂ] V) (h : ∀ x y, H (f x) y = H x (f' y)) :
    LinearMap.det f = conj (LinearMap.det f') := by
  classical
  let e := Module.finBasis ℂ V
  have hG := gram_det_ne_zero H hpos e
  have hfe : ∀ (g : V →ₗ[ℂ] V) j, g (e j) = ∑ k, LinearMap.toMatrix e e g k j • e k := fun g j => by
    simp only [LinearMap.toMatrix_apply]; exact (e.sum_repr (g (e j))).symm
  have hmat : (LinearMap.toMatrix e e f).transpose * (Matrix.of fun i j => H (e i) (e j))
      = (Matrix.of fun i j => H (e i) (e j)) * (LinearMap.toMatrix e e f').map (starRingEnd ℂ) := by
    ext i j
    have h1 := h (e i) (e j)
    rw [hfe f i, hfe f' j] at h1
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply]
    exact h1.trans (Finset.sum_congr rfl fun k _ => mul_comm _ _)
  have hc : ((LinearMap.toMatrix e e f').map (starRingEnd ℂ)).det
      = starRingEnd ℂ (LinearMap.toMatrix e e f').det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc] at hdet
  rw [← LinearMap.det_toMatrix e f, ← LinearMap.det_toMatrix e f']
  exact mul_right_cancel₀ hG (hdet.trans (mul_comm _ _))
end Formalism.L2.Th1.H.Cay
