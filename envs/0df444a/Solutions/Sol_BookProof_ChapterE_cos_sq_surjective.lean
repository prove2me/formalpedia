-- Prove2me | solution 1 for BookProof.ChapterE.cos_sq_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:26:53.449363+00:00
-- url     : https://prove2.me/submissions/7639a45b-2992-4858-b3e4-ad147b2190e9

-- Generated from ChapterE.lean — solution of BookProof.ChapterE.cos_sq_surjective
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE



open scoped Matrix BigOperators
open Filter
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ t : ℝ, Real.cos t ^ 2 = p := by

  refine ⟨ Real.arccos ( Real.sqrt p ), ?_ ⟩
  rw [ Real.cos_arccos ] <;> nlinarith [ Real.mul_self_sqrt hp0 ]
