-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.dirDeriv_dirDeriv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:19.776296+00:00
-- url     : https://prove2.me/submissions/08cea277-1471-4bf5-8255-51b013759bc3

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.dirDeriv_dirDeriv
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Theorems.Thm_BookProof_NavierStokesEulerian_dirDeriv_eq
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution (f : (Fin 3 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (j k : Fin 3)
    (x : Fin 3 → ℝ) :
    dirDeriv (dirDeriv f j) k x = fderiv ℝ (fderiv ℝ f) x (evec k) (evec j) := by

  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfd : dirDeriv f j = fun y => fderiv ℝ f y (evec j) := funext fun y =>
    dirDeriv_eq (hf.differentiable (by norm_num) y).hasFDerivAt j
  have hg : HasFDerivAt (fun y => fderiv ℝ f y (evec j))
      ((ContinuousLinearMap.apply ℝ ℝ (evec j)).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ (evec j)).hasFDerivAt.comp x (hd x).hasFDerivAt
  rw [hfd]
  simpa using dirDeriv_eq hg k
