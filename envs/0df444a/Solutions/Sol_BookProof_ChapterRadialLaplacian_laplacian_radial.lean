-- Prove2me | solution 1 for BookProof.ChapterRadialLaplacian.laplacian_radial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:22.088346+00:00
-- url     : https://prove2.me/submissions/4294520f-d071-470b-b4e2-2d672968b3e5

-- Generated from ChapterRadialLaplacian.lean — solution of BookProof.ChapterRadialLaplacian.laplacian_radial
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Theorems.Thm_BookProof_ChapterRadialLaplacian_laplacian_comp_normSq
import Theorems.Thm_BookProof_ChapterRadialLaplacian_deriv_sqrt_comp
open BookProof.ChapterRadialLaplacian




open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℝ E] {g : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hg : ContDiffAt ℝ 2 g ‖x‖) :
    (Δ fun y : E => g ‖y‖) x
      = deriv (deriv g) ‖x‖
        + (((Module.finrank ℝ E : ℝ) - 1) / ‖x‖) * deriv g ‖x‖ := by

  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr' : ‖x‖ ≠ 0 := ne_of_gt hr
  have hsq : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq (norm_nonneg x)
  have hfun : (fun y : E => g ‖y‖) = fun y : E => g (Real.sqrt (‖y‖ ^ 2)) := by
    funext y; rw [Real.sqrt_sq (norm_nonneg y)]
  have hG : ContDiffAt ℝ 2 (fun q => g (Real.sqrt q)) (‖x‖ ^ 2) := by
    have hsqrt : ContDiffAt ℝ 2 (fun q : ℝ => Real.sqrt q) (‖x‖ ^ 2) :=
      Real.contDiffAt_sqrt (pow_ne_zero 2 hr')
    have : ContDiffAt ℝ 2 g (Real.sqrt (‖x‖ ^ 2)) := by rw [hsq]; exact hg
    exact this.comp (‖x‖ ^ 2) hsqrt
  obtain ⟨hd1, hd2⟩ := deriv_sqrt_comp hr hg
  rw [hfun, laplacian_comp_normSq hG, hd1, hd2]
  field_simp
  ring
