-- Prove2me | solution 1 for BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:41:32.06544+00:00
-- url     : https://prove2.me/submissions/03e050b2-7a00-4f0e-81ee-8a3de54897a7

-- Generated from ChapterRadialLaplacian.lean — solution of BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Theorems.Thm_BookProof_ChapterRadialLaplacian_helmholtz_sbessel_zero
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterRadialLaplacian




open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace
open BookProof.ChapterSphericalBessel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in

theorem solution {p : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : EuclideanSpace ℝ (Fin 3) => sbessel 0 (p * ‖y‖)) x
      = p ^ 2 * sbessel 0 (p * ‖x‖) :=
  helmholtz_sbessel_zero (by simp) hp hx
