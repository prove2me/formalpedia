-- Prove2me | solution 1 for BookProof.ChapterLaplacianProduct.fderiv_radial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:40.694693+00:00
-- url     : https://prove2.me/submissions/91769561-d0b9-47e6-a251-4b25b6438cd5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterLaplacianProduct.lean — solution of BookProof.ChapterLaplacianProduct.fderiv_radial
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
import Theorems.Thm_BookProof_ChapterRadialLaplacian_deriv_sqrt_comp
import Theorems.Thm_BookProof_ChapterRadialLaplacian_fderiv_comp_normSq
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct




open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) :
    fderiv ℝ (fun y : E => g ‖y‖) x = (deriv g ‖x‖ / ‖x‖) • innerCLM E x := by

  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq (norm_nonneg x)
  have hfun : (fun y : E => g ‖y‖) = fun y : E => (fun q => g (Real.sqrt q)) (‖y‖ ^ 2) := by
    funext y; simp [Real.sqrt_sq (norm_nonneg y)]
  have hG : ContDiffAt ℝ 2 (fun q => g (Real.sqrt q)) (‖x‖ ^ 2) := by
    have hsqrt : ContDiffAt ℝ 2 (fun q : ℝ => Real.sqrt q) (‖x‖ ^ 2) :=
      Real.contDiffAt_sqrt (pow_ne_zero 2 (ne_of_gt hr))
    have h : ContDiffAt ℝ 2 g (Real.sqrt (‖x‖ ^ 2)) := by rw [hsq]; exact hg
    exact h.comp (‖x‖ ^ 2) hsqrt
  obtain ⟨hd1, -⟩ := deriv_sqrt_comp hr hg
  rw [hfun, (fderiv_comp_normSq hG).self_of_nhds]
  simp only [hd1]
  congr 1
  field_simp
