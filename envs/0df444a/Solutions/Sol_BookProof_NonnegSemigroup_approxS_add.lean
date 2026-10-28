-- Prove2me | solution 1 for BookProof.NonnegSemigroup.approxS_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T15:08:29.18327+00:00
-- url     : https://prove2.me/submissions/90f47aac-0fda-4cf1-a87b-0f255891c248

-- Generated from ChapterNonnegSemigroup.lean — solution of BookProof.NonnegSemigroup.approxS_add
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup
import Theorems.Thm_BookProof_NonnegSemigroup_expNeg_add
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
variable {T : Submodule ℂ (F × F)}

set_option maxHeartbeats 1000000 in
theorem solution (hT : IsNonnegSelfAdjoint T) (n : ℕ) (s t : ℝ) :
    approxS hT n (s + t) = approxS hT n s * approxS hT n t := expNeg_add _ s t
