-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.ext_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:08.351531+00:00
-- url     : https://prove2.me/submissions/4ed595fd-3602-4fc3-abe3-df06000638a0

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_monomial
import Theorems.Thm_Formalism_CountingSumsFrames_TO_sl_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (x : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : ∀ m ∈ x.support, ltr fs m ∈ S) : ext fs φ x = ∑ m ∈ S, φ (slc fs m x) * monomial m 1 := by
  conv_lhs => rw [x.as_sum]
  conv_rhs => rw [x.as_sum]
  simp_rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp_rw [sl_monomial, apply_ite φ, map_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq S (ltr fs d), if_pos (hS d hd), ext_monomial]
  have h1 : (monomial (frst fs d) (coeff d x) : MvPolynomial σ K) = coeff d x • monomial (frst fs d) 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_mul_assoc]
end Formalism.CountingSumsFrames.TO
