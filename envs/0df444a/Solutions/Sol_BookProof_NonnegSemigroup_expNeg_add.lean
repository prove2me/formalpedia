-- Prove2me | solution 1 for BookProof.NonnegSemigroup.expNeg_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T14:56:14.835388+00:00
-- url     : https://prove2.me/submissions/72ea3cf9-29a1-411f-8892-c3748a2e3eea

-- Generated from ChapterNonnegSemigroup.lean — solution of BookProof.NonnegSemigroup.expNeg_add
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
open BookProof.NonnegSemigroup




open BookProof.ClosureUniqueness BookProof.PositiveSquareRoot BookProof.NonnegResolvent
open BookProof.NonnegUnitaryGroup
open Filter Topology NormedSpace
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

noncomputable local instance ratNormedAlgebra' : NormedAlgebra ℚ (F →L[ℂ] F) :=
  NormedAlgebra.restrictScalars ℚ ℂ (F →L[ℂ] F)

set_option maxHeartbeats 1000000 in
theorem solution (A : F →L[ℂ] F) (s t : ℝ) :
    expNeg A (s + t) = expNeg A s * expNeg A t := by

  have hc : Commute ((-s : ℝ) • A) ((-t : ℝ) • A) :=
    ((Commute.refl A).smul_right _).smul_left _
  have hsum : ((-(s + t) : ℝ) • A) = ((-s : ℝ) • A) + ((-t : ℝ) • A) := by
    rw [← add_smul]; congr 1; ring
  simp only [expNeg, hsum, NormedSpace.exp_add_of_commute hc]
