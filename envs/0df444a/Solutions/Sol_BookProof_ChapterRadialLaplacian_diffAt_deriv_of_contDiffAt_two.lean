-- Prove2me | solution 1 for BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:39:53.658891+00:00
-- url     : https://prove2.me/submissions/9523fe92-ae78-4fba-8e6f-9e8e1a4fc7e3

-- Generated from ChapterRadialLaplacian.lean — solution of BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian




open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {G : ℝ → ℝ} {q : ℝ} (h : ContDiffAt ℝ 2 G q) :
    DifferentiableAt ℝ (deriv G) q := by

  obtain ⟨u, hu, hGu⟩ := h.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨v, hvu, hvo, hqv⟩ := mem_nhds_iff.1 hu
  have h2 : ContDiffOn ℝ 1 (deriv G) v := (hGu.mono hvu).deriv_of_isOpen hvo (by norm_num)
  exact (h2.differentiableOn (by norm_num)).differentiableAt (hvo.mem_nhds hqv)
