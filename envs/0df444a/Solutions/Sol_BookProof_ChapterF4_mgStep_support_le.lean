-- Prove2me | solution 1 for BookProof.ChapterF4.mgStep_support_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:03:31.312154+00:00
-- url     : https://prove2.me/submissions/e5567049-8941-4ad0-a83f-0f54a3ad48e8

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.mgStep_support_le
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (st : (ι → ℕ) × ℕ) (x : ι)
    (h : mgSupport st.1 ≤ k) : mgSupport (mgStep k st x).1 ≤ k := by

      unfold mgStep;
      split_ifs;
      · unfold mgSupport at *;
        convert h using 2 ; ext a ; by_cases ha : a = x <;> simp [ *, Function.update_apply ];
      · refine le_trans ?_ ‹_›;
        exact Finset.card_le_card ( show Finset.filter ( fun a => 0 < ( Function.update st.1 x 1 ) a
            ) Finset.univ ⊆ Finset.filter ( fun a => 0 < st.1 a ) Finset.univ ∪ { x } from fun a ha
                => by
          by_cases ha' : a = x <;> aesop ) |> le_trans <| Finset.card_union_le _ _;
      · refine le_trans ?_ h;
        refine Finset.card_le_card ?_;
        grind
