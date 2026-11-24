-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.LFocks_subAdj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:37.613568+00:00
-- url     : https://prove2.me/submissions/90817b17-c2d6-4122-87f8-03d40aa56c78

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_mul_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_C_mul_right
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_constantCoeff_sub
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_pderiv_sub
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_sub_C
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_sub_X
import Theorems.Thm_Formalism_REAL_fischerInner_X_mul_left
import Theorems.Thm_Formalism_REAL_fischerInner_sum_left
import Theorems.Thm_Formalism_REAL_fischerInner_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ : Type*} [Fintype σ] [DecidableEq σ] (U : Matrix σ σ ℂ)
    (f g : MvPolynomial σ ℂ) :
    fockF (sub U f) g = fockF f (sub U.conjTranspose g) := by
  induction f using MvPolynomial.induction_on generalizing g
  · rename_i a
    rw [LFocks_sub_C, LFocks_C_left, LFocks_C_left,
      LFocks_constantCoeff_sub]
  · rename_i p q hp hq
    rw [map_add, Formalism.REAL.fischerInner_add_left, Formalism.REAL.fischerInner_add_left, hp, hq]
  · rename_i p i hp
    rw [map_mul, LFocks_sub_X, mul_comm p (X i), Formalism.REAL.fischerInner_X_mul_left i p,
      LFocks_pderiv_sub, Formalism.REAL.fischerInner_sum_right, Finset.mul_sum, Formalism.REAL.fischerInner_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LFocks_C_mul_right, ← hp, Matrix.conjTranspose_apply, star_star,
      mul_comm (sub U p), mul_assoc, LFocks_C_mul_left,
      Formalism.REAL.fischerInner_X_mul_left]
end Formalism.GradedWeylDivisibility
