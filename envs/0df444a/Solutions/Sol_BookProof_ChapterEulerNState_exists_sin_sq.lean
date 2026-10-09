-- Prove2me | solution 1 for BookProof.ChapterEulerNState.exists_sin_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:50:25.753893+00:00
-- url     : https://prove2.me/submissions/ace67400-78c3-4041-a366-38b3b1345a20

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.exists_sin_sq
import Mathlib
import Definitions.Def_ChapterEulerNState
import Theorems.Thm_BookProof_ChapterEulerNState_exists_cos_sq
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ∃ θ : ℝ, Real.sin θ ^ 2 = q := by

  obtain ⟨θ, hθ⟩ := exists_cos_sq h0 h1
  refine ⟨θ + Real.pi / 2, ?_⟩
  rw [Real.sin_add]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  nlinarith [hθ]
