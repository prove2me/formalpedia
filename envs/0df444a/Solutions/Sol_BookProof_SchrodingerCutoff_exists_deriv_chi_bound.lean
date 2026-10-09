-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.exists_deriv_chi_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:52:43.605002+00:00
-- url     : https://prove2.me/submissions/5187519a-0717-41e4-9b66-d180c0bd8f92

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.exists_deriv_chi_bound
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_deriv_chi_continuous
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ y, |deriv chi y| ≤ C := by

  have hc : Continuous fun y => |deriv chi y| := deriv_chi_continuous.abs
  have hs : HasCompactSupport fun y => |deriv chi y| :=
    (bump0.hasCompactSupport.deriv).abs
  obtain ⟨y0, hy0⟩ := hc.exists_forall_ge_of_hasCompactSupport hs
  exact ⟨|deriv chi y0| + 1, by positivity, fun y => by linarith [hy0 y]⟩
