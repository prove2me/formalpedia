-- Prove2me | solution 1 for Formalism.CountingSumsFrames.direct_sum_partners
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:30.573053+00:00
-- url     : https://prove2.me/submissions/95d4c0a2-ff02-44bc-acc6-7de2d2d5701b

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
theorem _root_.solution : DirectSumPartners := by
  intro O _ _ _ π _ M A B _ _ _ _ b n g D hsat hprim
  constructor
  · intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨z, hz⟩ := hx
    have hd : ∀ d, x d ∈ LinearMap.range (g d) := by
      intro d
      apply hsat d
      rw [LinearMap.mem_range]
      refine ⟨z d, ?_⟩
      have := congrFun hz d
      simpa using this
    choose w hw using fun d => LinearMap.mem_range.mp (hd d)
    rw [LinearMap.mem_range]
    refine ⟨w, funext fun d => ?_⟩
    simpa using hw d
  · rintro x ⟨d₀, i, hi⟩
    obtain ⟨u₀, hu₀⟩ := hprim d₀ (x d₀) ⟨i, hi⟩
    refine ⟨Pi.single d₀ u₀, ?_⟩
    rw [Finset.sum_eq_single d₀]
    · simpa using hu₀
    · intro d _ hd
      rw [Pi.single_eq_of_ne hd, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
end Formalism.CountingSumsFrames
