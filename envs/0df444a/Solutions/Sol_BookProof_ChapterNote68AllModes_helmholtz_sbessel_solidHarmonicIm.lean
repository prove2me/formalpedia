-- Prove2me | solution 1 for BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonicIm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:01:38.843175+00:00
-- url     : https://prove2.me/submissions/24994fd6-bda3-4f49-b9c3-75cacdc1cb6b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNote68AllModes.lean — solution of BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonicIm
import Mathlib
import Definitions.Def_ChapterNote68AllModes
import Theorems.Thm_BookProof_ChapterBesselHarmonic_helmholtz_sbessel_harmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_solidHarmonicIm
import Theorems.Thm_BookProof_ChapterSolidHarmonic_solidHarmonicIm_euler
import Theorems.Thm_BookProof_ChapterSolidHarmonic_solidHarmonicIm_harmonic
import Definitions.Def_ChapterBesselHarmonic
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterNote68AllModes




open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterSphericalBessel BookProof.ChapterBesselHarmonic
open BookProof.ChapterSolidHarmonic
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)
    (h3 : Module.finrank ℝ E = 3) {l μ : ℕ} (hμ : μ ≤ l) {x : E} {p : ℝ}
    (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : E => (sbessel l (p * ‖y‖) / ‖y‖ ^ l) * solidHarmonicIm u v e l μ y) x
      = p ^ 2 * ((sbessel l (p * ‖x‖) / ‖x‖ ^ l) * solidHarmonicIm u v e l μ x) :=
  helmholtz_sbessel_harmonic h3 hp hx (contDiff_solidHarmonicIm u v e l μ).contDiffAt
      (solidHarmonicIm_harmonic hu hv he huv hue hve h3 hμ x) (solidHarmonicIm_euler u v e hμ x)
