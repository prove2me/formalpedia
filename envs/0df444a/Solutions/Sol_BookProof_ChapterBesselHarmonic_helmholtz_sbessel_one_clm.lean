-- Prove2me | solution 1 for BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:16:19.068465+00:00
-- url     : https://prove2.me/submissions/48167c08-e8bb-4654-9973-7c6cefc3335e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterBesselHarmonic.lean — solution of BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm
import Mathlib
import Definitions.Def_ChapterBesselHarmonic
import Theorems.Thm_BookProof_ChapterBesselHarmonic_helmholtz_sbessel_harmonic
import Theorems.Thm_BookProof_ChapterLaplacianProduct_euler_clm
import Theorems.Thm_BookProof_ChapterLaplacianProduct_harmonic_clm
open BookProof.ChapterBesselHarmonic




open Filter Laplacian InnerProductSpace
open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3)
    (L : E →L[ℝ] ℝ) {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : E => (sbessel 1 (p * ‖y‖) / ‖y‖ ^ 1) * L y) x
      = p ^ 2 * ((sbessel 1 (p * ‖x‖) / ‖x‖ ^ 1) * L x) :=
  helmholtz_sbessel_harmonic h3 hp hx
      (L.contDiff (n := 2)).contDiffAt (harmonic_clm L x) (euler_clm L x)
