-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.ext_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:31.755808+00:00
-- url     : https://prove2.me/submissions/36ab8fa2-9219-4afb-97cd-d99e6b893d12

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_frst_of
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ltr_of
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_frst_of__a64a2b7f77bf
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_ltr_of__5656358b1af2
import Theorems.Thm_Formalism_CountingSumsFrames_TO_frst_add
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ltr_add
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_monomial

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
theorem _root_.solution (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) {g q : MvPolynomial σ K} (hg : IsF fs g)
    (hq : IsL fs q) : ext fs φ (g * q) = φ g * q := by
  classical
  rw [g.as_sum, q.as_sum, Finset.sum_mul_sum, map_sum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [monomial_mul, ext_monomial, frst_add, ltr_add, frst_of fs (hg a ha), ltr_of fs (hg a ha),
    frst_of' fs (hq b hb), ltr_of' fs (hq b hb), add_zero, zero_add]
  have h1 : (monomial a (coeff a g) : MvPolynomial σ K) = coeff a g • monomial a 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  have h2 : (monomial b (coeff b q) : MvPolynomial σ K) = coeff b q • monomial b 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1, h2, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
end Formalism.CountingSumsFrames.TO
