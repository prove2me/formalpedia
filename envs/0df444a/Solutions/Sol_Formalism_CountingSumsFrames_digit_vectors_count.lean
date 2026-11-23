-- Prove2me | solution 1 for Formalism.CountingSumsFrames.digit_vectors_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:55.084049+00:00
-- url     : https://prove2.me/submissions/0740bc63-875c-45f5-a65d-20dcbb2d82c6

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Theorems.Thm_Formalism_CountingSumsFrames_digit_one_letter

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
theorem _root_.solution : DigitVectorsCount := by
  intro s m P aa hP
  have e : ((univ : Finset (DigitVec s m P)).filter (fun ρ => DigitCompat ρ aa)) =
      Fintype.piFinset (fun i => (univ : Finset (Fin (m+1) → Fin (P i))).filter
        (fun f => (∑ c, (f c : ℕ)) % P i = aa i.castSucc % P i)) := by
    ext ρ
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter]
    rfl
  rw [e, Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun i _ => digit_one_letter (P i) m (aa i.castSucc) (hP i)
end Formalism.CountingSumsFrames
