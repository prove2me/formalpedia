-- Prove2me | solution 1 for Formalism.CountingSumsFrames.share_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:23.916802+00:00
-- url     : https://prove2.me/submissions/e815d656-10b7-41e9-830c-205b3b53eb1f

import Definitions.Def_Formalism_PolynomialDimension_EdgeSumGoodRank
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DvdPowOfNotPowSuccDvd
import Theorems.Thm_Formalism_CountingSumsFrames_one_sub_sum_mul_prod_le_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : ShareProd := by
  intro J κ n d hκ h
  push_cast
  exact one_sub_sum_mul_prod_le_prod Finset.univ κ (fun j => (n j : ℝ)) (fun j => (d j : ℝ)) hκ (fun j => Nat.cast_nonneg _) h
end Formalism.CountingSumsFrames
