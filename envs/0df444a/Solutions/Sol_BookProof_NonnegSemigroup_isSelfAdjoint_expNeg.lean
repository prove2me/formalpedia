-- Prove2me | solution 1 for BookProof.NonnegSemigroup.isSelfAdjoint_expNeg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T14:56:16.002601+00:00
-- url     : https://prove2.me/submissions/f154eec0-3706-43bc-aecc-faf944c62b9b

-- Generated from ChapterNonnegSemigroup.lean — solution of BookProof.NonnegSemigroup.isSelfAdjoint_expNeg
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

set_option maxHeartbeats 1000000 in
theorem solution {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (t : ℝ) :
    IsSelfAdjoint (expNeg A t) := by

  have hstar : IsSelfAdjoint ((-t : ℝ) • A) := by
    change star ((-t : ℝ) • A) = (-t : ℝ) • A
    rw [star_smul, hA.star_eq]
    simp
  exact hstar.exp
