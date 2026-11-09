-- Prove2me | solution 1 for BookProof.QuadraticRotation.integral_comp_rotIso
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:58:37.564031+00:00
-- url     : https://prove2.me/submissions/f3b5af45-3f97-4a98-9d74-802ffe0153e5

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.integral_comp_rotIso
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (g : Vd d → ℂ) : ∫ x : Vd d, g (rotIso hO x) = ∫ y : Vd d, g y :=
  (rotIso hO).measurePreserving.integral_comp
      ((rotIso hO).toHomeomorph.measurableEmbedding) g
