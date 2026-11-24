-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ext_wh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:11.446687+00:00
-- url     : https://prove2.me/submissions/1f427317-0278-4817-a1c3-3745a4f9aef0

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_frst_add_ltr
import Theorems.Thm_Formalism_CountingSumsFrames_frst_isF
import Theorems.Thm_Formalism_CountingSumsFrames_ext_monomial
import Theorems.Thm_Formalism_CountingSumsFrames_weight_first
import Theorems.Thm_Formalism_CountingSumsFrames_wh_first

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
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφw : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν → φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν)
    (hφF : ∀ x, IsF (fsj N r j0) (φ x)) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν) :
    ext (fsj N r j0) φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m' hm' => ?_
  rw [ext_monomial]
  refine Submodule.smul_mem _ _ ?_
  have h1 : Finsupp.weight (wv L J) m' = ν := hx (mem_support_iff.mp hm')
  have hf : φ (monomial (frst (fsj N r j0) m') 1) ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J)
      (Finsupp.weight (wv L J) (frst (fsj N r j0) m')) := by
    rw [weight_first L hJ _ (frst_isF _ m')]
    exact wh_first L hJ (hφF _) (hφw _ _ (isWeightedHomogeneous_monomial _ _ _ rfl))
  have hl : IsWeightedHomogeneous (wv L J) (monomial (ltr (fsj N r j0) m') (1 : ℚ_[p]))
      (Finsupp.weight (wv L J) (ltr (fsj N r j0) m')) := isWeightedHomogeneous_monomial _ _ _ rfl
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  rw [← h1]
  conv_rhs => rw [← frst_add_ltr (fsj N r j0) m']
  rw [map_add]
  exact hf.mul hl
end Formalism.CountingSumsFrames
