-- Prove2me | solution 1 for BookProof.QuadraticRotation.polyGaussCore_dense_L2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:58:45.083883+00:00
-- url     : https://prove2.me/submissions/23d3e21d-b760-490b-87dc-a1928021bbef

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.polyGaussCore_dense_L2
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
theorem solution :
    Dense ((polyGaussCore (d := d) : Submodule ℂ (L2d d)) : Set (L2d d)) := polyGaussCore_dense
