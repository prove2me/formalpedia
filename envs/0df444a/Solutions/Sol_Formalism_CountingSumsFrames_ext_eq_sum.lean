-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ext_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:35.295851+00:00
-- url     : https://prove2.me/submissions/f09fd0ca-17dd-4238-a83d-46bd27349018

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_ext_monomial
import Theorems.Thm_Formalism_CountingSumsFrames_sl_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (x : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : ∀ m ∈ x.support, ltr fs m ∈ S) : ext fs φ x = ∑ m ∈ S, φ (slc fs m x) * monomial m 1 := by
  classical
  have e : ∀ m' ∈ x.support, ext fs φ (monomial m' (coeff m' x)) =
      ∑ m ∈ S, φ (slc fs m (monomial m' (coeff m' x))) * monomial m 1 := by
    intro m' hm'
    simp_rw [sl_monomial]
    rw [Finset.sum_eq_single (ltr fs m') (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, zero_mul])
      (fun h => absurd (hS m' hm') h), if_pos rfl, ext_monomial, ← smul_mul_assoc, ← map_smul, smul_monomial,
      smul_eq_mul, mul_one]
  conv_lhs => rw [x.as_sum]
  rw [map_sum, Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← x.as_sum]
end Formalism.CountingSumsFrames
