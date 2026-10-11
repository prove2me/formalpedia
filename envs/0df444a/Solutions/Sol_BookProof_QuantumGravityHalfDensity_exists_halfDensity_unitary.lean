-- Prove2me | solution 1 for BookProof.QuantumGravityHalfDensity.exists_halfDensity_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:39:39.158263+00:00
-- url     : https://prove2.me/submissions/c7d0429a-9aa2-48e0-b1fd-c77b59ecb75c

-- Generated from ChapterQuantumGravityHalfDensity.lean — solution of BookProof.QuantumGravityHalfDensity.exists_halfDensity_unitary
import Mathlib
import Definitions.Def_ChapterQuantumGravityHalfDensity
open BookProof.QuantumGravityHalfDensity




open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ _W : Lp ℂ 2 (volume.restrict (Set.Ioi (0 : ℝ))) ≃ₗᵢ[ℂ] Lp ℂ 2 qgSrcMeasure, True := ⟨halfDensityUnitary, trivial⟩
