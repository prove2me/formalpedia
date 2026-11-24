-- Prove2me | solution 1 for Formalism.CountingSumsFrames.slc_wh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:14.858986+00:00
-- url     : https://prove2.me/submissions/003459d8-0969-4efc-8acc-52662177673f

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_frst_add_ltr
import Theorems.Thm_Formalism_CountingSumsFrames_ltr_isL
import Theorems.Thm_Formalism_CountingSumsFrames_sl_monomial
import Theorems.Thm_Formalism_CountingSumsFrames_weight_wv_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (m : Fin N × Fin r →₀ ℕ) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν) :
    slc (fsj N r j0) m x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m' hm' => ?_
  rw [sl_monomial]
  split_ifs
  · rw [mem_weightedHomogeneousSubmodule]
    apply isWeightedHomogeneous_monomial
    have h1 : Finsupp.weight (wv L J) m' = ν := hx (mem_support_iff.mp hm')
    have h2 := weight_wv_zero L hJ (ltr (fsj N r j0) m') (ltr_isL _ m')
    rw [← h1]
    conv_rhs => rw [← frst_add_ltr (fsj N r j0) m']
    rw [map_add, h2, add_zero]
  · exact Submodule.zero_mem _
end Formalism.CountingSumsFrames
