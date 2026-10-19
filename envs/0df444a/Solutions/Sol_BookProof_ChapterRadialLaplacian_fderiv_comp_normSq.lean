-- Prove2me | solution 1 for BookProof.ChapterRadialLaplacian.fderiv_comp_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:39:54.688977+00:00
-- url     : https://prove2.me/submissions/36f0036c-d2c6-4acf-9010-f225432baf62

-- Generated from ChapterRadialLaplacian.lean — solution of BookProof.ChapterRadialLaplacian.fderiv_comp_normSq
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Theorems.Thm_BookProof_ChapterRadialLaplacian_hasFDerivAt_normSq
open BookProof.ChapterRadialLaplacian




open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) :
    (fderiv ℝ fun z : E => G (‖z‖ ^ 2)) =ᶠ[nhds x]
      fun y => (2 * deriv G (‖y‖ ^ 2)) • (innerCLM E y) := by

  have hcont : Continuous fun y : E => ‖y‖ ^ 2 := continuous_norm.pow 2
  have hev : ∀ᶠ q in nhds (‖x‖ ^ 2), DifferentiableAt ℝ G q := by
    filter_upwards [hG.eventually (by simp)] with q hq using hq.differentiableAt (by norm_num)
  have hevx : ∀ᶠ y in nhds x, DifferentiableAt ℝ G (‖y‖ ^ 2) :=
    (hcont.continuousAt (x := x)).eventually hev
  filter_upwards [hevx] with y hy
  have hcomp : HasFDerivAt (fun z : E => G (‖z‖ ^ 2))
      ((deriv G (‖y‖ ^ 2)) • ((2 : ℝ) • innerCLM E y)) y :=
    (hy.hasDerivAt).comp_hasFDerivAt y (hasFDerivAt_normSq y)
  rw [hcomp.fderiv, smul_smul]
  ring_nf
