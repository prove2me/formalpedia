-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.wh_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:59.487809+00:00
-- url     : https://prove2.me/submissions/0478c1dc-e022-4b0c-a657-8159f69b1bca

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_weight_first

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) {ν : Fin r → ℤ} {y : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hF : IsF (fsj N r j0) y) (hy : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hy ⊢
  intro d hd
  rw [weight_first L hJ d (hF d (mem_support_iff.mpr hd))]
  exact hy hd
end Formalism.CountingSumsFrames.TO
