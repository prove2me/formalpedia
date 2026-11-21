-- Prove2me | solution 1 for ExactDFTRefine.Main.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T03:00:19.906672+00:00
-- url     : https://prove2.me/submissions/4b32ca42-f079-4a3d-be57-a26a68e6b32b

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

theorem _root_.solution :
    moment 1 blocksP = 239134 ∧ moment 1 targetsT = 239886 ∧
    Multiset.card targetsT = 10928 := by
  have h_moment : ∀ (t : ℝ) (A : Multiset ℕ),
      moment t A = (A.map (fun r : ℕ => (r : ℝ) ^ t)).sum := by
    intro t A
    unfold moment
    simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton,
      Multiset.map_map, Function.comp_apply]
  have h_add : ∀ (A B : Multiset ℕ),
      moment 1 (A + B) = moment 1 A + moment 1 B := by
    intro A B
    rw [h_moment, h_moment, h_moment]
    simp only [Multiset.map_add, Multiset.sum_add, Real.rpow_one]
  have h_rep : ∀ (k r : ℕ),
      moment 1 (Multiset.replicate k r) = (k : ℝ) * (r : ℝ) := by
    intro k r
    rw [h_moment]
    simp only [Multiset.map_replicate, Multiset.sum_replicate, Real.rpow_one,
      nsmul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [blocksP, h_add, h_rep]
    norm_num
  · simp only [targetsT, h_add, h_rep]
    norm_num
  · simp only [targetsT, Multiset.card_add, Multiset.card_replicate]

end ExactDFTRefine.Main
