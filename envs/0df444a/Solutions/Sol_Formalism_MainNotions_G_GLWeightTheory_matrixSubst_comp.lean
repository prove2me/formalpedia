-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:23.932093+00:00
-- url     : https://prove2.me/submissions/3ddfd51d-ff70-4956-b1b5-2bcc39368d80

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_C
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (φ : R →+* B) (m1 m1' m2 m2' : Matrix (Fin n) (Fin n) B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S (RingHom.id B) m1 m1' (matrixSubst LL S φ m2 m2' F) = matrixSubst LL S φ (m1 * m2) (m2' * m1') F := by
  classical
  have : (matrixSubst LL S (RingHom.id B) m1 m1').comp (matrixSubst LL S φ m2 m2') =
      matrixSubst LL S φ (m1 * m2) (m2' * m1') := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [matrixSubst_C]
    · intro v
      rw [RingHom.comp_apply, matrixSubst_X, matrixSubst_X]
      by_cases hS : v.1 ∈ S
      · by_cases hv : LL.vec v.1 = true
        · rw [if_pos hS, if_pos hv, if_pos hS, if_pos hv, map_sum]
          have h1 : ∀ b : Fin n, matrixSubst LL S (RingHom.id B) m1 m1' (C (m2 b v.2) * X (v.1, b)) =
              ∑ a : Fin n, C (m1 a b * m2 b v.2) * X (v.1, a) := by
            intro b
            rw [map_mul, matrixSubst_C, matrixSubst_X, if_pos hS, if_pos hv, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [RingHom.id_apply, map_mul]; ring
          simp only [h1]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
        · rw [if_pos hS, if_neg hv, if_pos hS, if_neg hv, map_sum]
          have h1 : ∀ b : Fin n, matrixSubst LL S (RingHom.id B) m1 m1' (C (m2' v.2 b) * X (v.1, b)) =
              ∑ a : Fin n, C (m2' v.2 b * m1' b a) * X (v.1, a) := by
            intro b
            rw [map_mul, matrixSubst_C, matrixSubst_X, if_pos hS, if_neg hv, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [RingHom.id_apply, map_mul]; ring
          simp only [h1]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
      · rw [if_neg hS, if_neg hS, matrixSubst_X, if_neg hS]
  exact congrArg (fun f => f F) this
end Formalism.MainNotions.G.GLWeightTheory
