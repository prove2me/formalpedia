-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.pow4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:46.105178+00:00
-- url     : https://prove2.me/submissions/9fe6b5d2-5fff-4787-9d94-ef7760af11f8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_zero_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.IsQuadFn
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
namespace Formalism.L2.Th1.H.IsQuadFn
theorem _root_.solution (h : IsQuadFn φ b) :
    IsQuadFn (fun v : Fin 4 → M => ∏ i, φ (v i)) (fun v w => ∏ i, b (v i) (w i)) where
  add v w := by simp only [Pi.add_apply, h.add, Finset.prod_mul_distrib]
  left u v w := by simp only [Pi.add_apply, h.left, Finset.prod_mul_distrib]
  sq k v := by simp only [Pi.smul_apply, h.sq, Finset.prod_pow]
  ne v := Finset.prod_ne_zero_iff.2 fun i _ => h.ne _
  nondeg v hv := by
    funext i
    apply h.nondeg
    intro y
    have h1 := hv (Pi.single i y)
    rw [Finset.prod_eq_single i] at h1
    · simpa using h1
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, h.b_zero_right]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
end Formalism.L2.Th1.H.IsQuadFn
