-- Prove2me | solution 1 for BookProof.ChapterG2.no_translation_invariant_unit_vector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:21:16.389801+00:00
-- url     : https://prove2.me/submissions/4bb587ed-f6de-45cb-ae44-fbbe37071732

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.no_translation_invariant_unit_vector
import Mathlib
import Definitions.Def_ChapterG2
import Theorems.Thm_BookProof_ChapterG2_translation_invariant_l2_eq_zero
open BookProof.ChapterG2



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution {G : Type*} [Group G] [Infinite G] :
    ¬ ∃ Ψ : lp (fun _ : G => ℂ) 2, ‖Ψ‖ = 1 ∧ ∀ g x : G, Ψ (g * x) = Ψ x := by

  rintro ⟨ Ψ, hnorm, hinv ⟩;
  have := translation_invariant_l2_eq_zero Ψ hinv; aesop;
