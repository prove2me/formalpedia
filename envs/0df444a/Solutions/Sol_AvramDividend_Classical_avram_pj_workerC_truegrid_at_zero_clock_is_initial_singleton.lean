-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_truegrid_at_zero_clock_is_initial_singleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:26:26.747233+00:00
-- url     : https://prove2.me/submissions/e4a9396b-ed15-4465-af24-ba4981a4e96d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open scoped NNReal ENNReal
open MeasureTheory Set AvramDividend.Classical
noncomputable section
theorem solution
    {Ω : Type*} (n k : ℕ) (ρ : Ω → ℝ≥0)
    (ω : Ω) (hzero : ρ ω = 0) :
    (((Finset.range (k + 1)).image
      (fun i : ℕ => min
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
        (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω))
      = ({0} : Finset ℝ≥0) := by 
  have hnonempty : (Finset.range (k + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩
  have heq : (fun i : ℕ => min
    ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
    (ρ ω)) = fun _ => (0 : ℝ≥0) := by
    funext i
    simp [hzero]
  rw [heq]
  simp [hzero, Finset.image_const, hnonempty]
