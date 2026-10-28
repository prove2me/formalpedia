-- Prove2me | solution 1 for BookProof.NonnegSemigroup.norm_semigroupS_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T14:56:18.540868+00:00
-- url     : https://prove2.me/submissions/b2bf8357-a4f6-4a48-b2ad-1ccd5ee4df41

-- Generated from ChapterNonnegSemigroup.lean — solution of BookProof.NonnegSemigroup.norm_semigroupS_apply_le
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
variable {T : Submodule ℂ (F × F)}

set_option maxHeartbeats 1000000 in
theorem solution (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    ‖semigroupS hT hsv ht x‖ ≤ ‖x‖ := norm_semigroupFun_le hT hsv ht x
