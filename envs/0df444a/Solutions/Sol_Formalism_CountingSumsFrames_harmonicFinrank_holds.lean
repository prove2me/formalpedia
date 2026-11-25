-- Prove2me | solution 1 for Formalism.CountingSumsFrames.harmonicFinrank_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:10.976056+00:00
-- url     : https://prove2.me/submissions/9e1fffd2-0298-4bc3-a3ed-3a660d0dd4ba

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_of_left
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_of_right
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_finrank_polAB
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_finrank_har
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
private theorem mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero {A B : ℕ} {f : PolXY K k} :
    f ∈ HarAB K k A B ↔ f ∈ PolAB K k A B ∧ ctrF K k f = 0 := Iff.rfl
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Har2
namespace Formalism.CountingSumsFrames
theorem _root_.solution : HarDim := by
  unfold HarDim
  intro K _ _ k' A B
  refine ⟨finrank_polAB k' A B, ?_, ?_, ?_⟩
  · rw [← finrank_polAB (K := K) k' A B, ← finrank_polAB (K := K) k' (A + 1) (B + 1)]
    exact finrank_har k' A B
  · ext f
    exact ⟨fun h => (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 h).1, har_of_right⟩
  · ext f
    exact ⟨fun h => (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 h).1, har_of_left⟩
end Formalism.CountingSumsFrames
