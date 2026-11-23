-- Prove2me | solution 1 for Formalism.CountingSumsFrames.direct_sum_good_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:30.550914+00:00
-- url     : https://prove2.me/submissions/9e251b13-6051-44f6-9095-433d13ba9c7c

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : DirectSumGoodRank := by
  intro O _ _ _ π _ M A B _ _ _ _ _ _ _ _ f n D hf
  choose u v huv using hf
  let e : (Σ d : Fin M, Fin (n d)) ≃ Fin (∑ d, n d) := finSigmaFinEquiv
  refine ⟨LinearMap.pi (fun d => u d ∘ₗ LinearMap.funLeft O O (fun j => e ⟨d, j⟩)),
    LinearMap.pi (fun k => LinearMap.proj (e.symm k).2 ∘ₗ v (e.symm k).1 ∘ₗ
      LinearMap.proj (e.symm k).1), ?_⟩
  apply LinearMap.ext
  intro x
  funext k
  have h2 := congrFun (LinearMap.congr_fun (huv (e.symm k).1) (fun j => x (e ⟨(e.symm k).1, j⟩)))
    (e.symm k).2
  exact h2.trans (by simp)
end Formalism.CountingSumsFrames
