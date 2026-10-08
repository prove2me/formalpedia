-- Prove2me | solution 1 for BookProof.QuantumGravityHalfDensity.halfDensityUnitary_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:56:56.295258+00:00
-- url     : https://prove2.me/submissions/90097309-5fc0-45e0-a17e-6afd6d852f95

-- Generated from ChapterQuantumGravityHalfDensity.lean — solution of BookProof.QuantumGravityHalfDensity.halfDensityUnitary_apply
import Mathlib
import Definitions.Def_ChapterQuantumGravityHalfDensity
open BookProof.QuantumGravityHalfDensity




open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (g : Lp ℂ 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    (halfDensityUnitary g : ℝ → ℂ) =ᵐ[qgSrcMeasure] fun y => (g : ℝ → ℂ) (y ^ 2) := Lp.coeFn_compMeasurePreserving _ measurePreserving_qgSquare
