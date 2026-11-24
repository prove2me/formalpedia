-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.eq_of_slc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:41.506084+00:00
-- url     : https://prove2.me/submissions/8f28ad56-b3ce-48a6-85cd-1491967feb61

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_eq_sum_sl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
    (x y : MvPolynomial σ K) (hxy : ∀ m, slc fs m x = slc fs m y) : x = y := by
  classical
  have hx := eq_sum_sl fs x ((x.support ∪ y.support).image (ltr fs))
    (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_left _ hm))
  have hy := eq_sum_sl fs y ((x.support ∪ y.support).image (ltr fs))
    (fun m hm => Finset.mem_image_of_mem _ (Finset.mem_union_right _ hm))
  exact hx.trans ((Finset.sum_congr rfl fun m _ => by rw [hxy m]).trans hy.symm)
end Formalism.CountingSumsFrames.TO
