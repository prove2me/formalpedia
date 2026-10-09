-- Prove2me | solution 1 for BookProof.ChapterEulerNState.exists_cos_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:50:12.433486+00:00
-- url     : https://prove2.me/submissions/5ea1d253-45b1-48ab-9e9d-a2f79a670c24

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.exists_cos_sq
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ∃ θ : ℝ, Real.cos θ ^ 2 = q :=
  ⟨Real.arccos (Real.sqrt q), by
      rw [Real.cos_arccos] <;> nlinarith [Real.mul_self_sqrt h0]⟩
