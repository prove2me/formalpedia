-- Prove2me | solution 1 for BookProof.ChapterSolovayTailDimension.substrate_infinite_dimensional
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T12:25:10.112277+00:00
-- url     : https://prove2.me/submissions/b5cd8643-d245-4d16-80a2-55421747b965

-- Generated from ChapterSolovayTailDimension.lean — solution of BookProof.ChapterSolovayTailDimension.substrate_infinite_dimensional
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
import Theorems.Thm_BookProof_ChapterSolovayTailDimension_substrateBasisVector_orthonormal
import Definitions.Def_PhysMeasureBasis
open BookProof.ChapterSolovayTailDimension



noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal
open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution : ¬ FiniteDimensional ℝ Substrate := by

  intro _
  haveI : Finite ℕ :=
    (substrateBasisVector_orthonormal.linearIndependent).finite_of_isNoetherian
  exact not_finite ℕ
