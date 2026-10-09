-- Prove2me | solution 1 for BookProof.ChapterG2.gauge_fixing_section_discontinuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:21:42.231889+00:00
-- url     : https://prove2.me/submissions/73318ce2-d1e7-4779-b2ce-ddd8f8fadbf4

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.gauge_fixing_section_discontinuous
import Mathlib
import Definitions.Def_ChapterG2
import Theorems.Thm_BookProof_ChapterG2_no_continuous_gauge_fixing_circle
open BookProof.ChapterG2



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution
    (s : Circle → ℝ) (hs : ∀ z, Circle.exp (s z) = z) : ¬ Continuous s := by

  contrapose! hs with hs;
  exact not_forall.mp fun h => no_continuous_gauge_fixing_circle ⟨ s, hs, h ⟩
