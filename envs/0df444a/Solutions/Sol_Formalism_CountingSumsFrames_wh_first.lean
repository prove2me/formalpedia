-- Prove2me | solution 1 for Formalism.CountingSumsFrames.wh_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:48.054919+00:00
-- url     : https://prove2.me/submissions/772e1c05-e5b4-48cd-bedd-87cd7c53fe01

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_weight_first

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
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) {ν : Fin r → ℤ} {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hF : IsF (fsj N r j0) y) (hy : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hy ⊢
  intro m hm
  rw [weight_first L hJ m (hF m (mem_support_iff.mpr hm))]
  exact hy hm
end Formalism.CountingSumsFrames
