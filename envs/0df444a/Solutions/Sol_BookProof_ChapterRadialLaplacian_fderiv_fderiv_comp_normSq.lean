-- Prove2me | solution 1 for BookProof.ChapterRadialLaplacian.fderiv_fderiv_comp_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:40:22.403594+00:00
-- url     : https://prove2.me/submissions/c5297113-e206-41ae-bb0e-1469493835e4

-- Generated from ChapterRadialLaplacian.lean — solution of BookProof.ChapterRadialLaplacian.fderiv_fderiv_comp_normSq
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Theorems.Thm_BookProof_ChapterRadialLaplacian_hasFDerivAt_normSq
import Theorems.Thm_BookProof_ChapterRadialLaplacian_diffAt_deriv_of_contDiffAt_two
import Theorems.Thm_BookProof_ChapterRadialLaplacian_fderiv_comp_normSq
open BookProof.ChapterRadialLaplacian




open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℝ E] {G : ℝ → ℝ} {x : E}
    (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) :
    fderiv ℝ (fderiv ℝ fun y : E => G (‖y‖ ^ 2)) x
      = (2 * deriv G (‖x‖ ^ 2)) • (innerCLM E)
        + ((4 * deriv (deriv G) (‖x‖ ^ 2)) • innerCLM E x).smulRight (innerCLM E x) := by

  have hc : HasFDerivAt (fun y : E => 2 * deriv G (‖y‖ ^ 2))
      ((4 * deriv (deriv G) (‖x‖ ^ 2)) • innerCLM E x) x := by
    have hd0 : HasFDerivAt ((deriv G) ∘ fun z : E => ‖z‖ ^ 2)
        ((deriv (deriv G) (‖x‖ ^ 2)) • ((2 : ℝ) • innerCLM E x)) x :=
      ((diffAt_deriv_of_contDiffAt_two hG).hasDerivAt).comp_hasFDerivAt x (hasFDerivAt_normSq x)
    have hd : HasFDerivAt (fun y : E => deriv G (‖y‖ ^ 2))
        ((2 * deriv (deriv G) (‖x‖ ^ 2)) • innerCLM E x) x := by
      rw [smul_smul] at hd0
      convert hd0 using 2 <;> (first | rfl | ring)
    have h2 := hd.const_mul (2 : ℝ)
    convert h2 using 1 <;> (first | rfl | (rw [smul_smul]; ring_nf))
  have hF : HasFDerivAt (fun y : E => (2 * deriv G (‖y‖ ^ 2)) • innerCLM E y)
      ((2 * deriv G (‖x‖ ^ 2)) • (innerCLM E)
        + ((4 * deriv (deriv G) (‖x‖ ^ 2)) • innerCLM E x).smulRight (innerCLM E x)) x :=
    hc.smul (innerCLM E).hasFDerivAt
  rw [(fderiv_comp_normSq hG).fderiv_eq, hF.fderiv]
