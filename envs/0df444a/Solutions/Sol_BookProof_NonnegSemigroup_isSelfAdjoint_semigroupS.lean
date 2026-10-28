-- Prove2me | solution 1 for BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T15:08:31.446644+00:00
-- url     : https://prove2.me/submissions/1b3ae181-5b77-42ac-8245-f8aa7206141f

-- Generated from ChapterNonnegSemigroup.lean — solution of BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup
import Theorems.Thm_BookProof_NonnegSemigroup_isSelfAdjoint_approxS
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
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (semigroupS hT hsv ht) := by

  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hx := (tendsto_semigroupS hT hsv ht x).inner (𝕜 := ℂ) (tendsto_const_nhds (x := y))
  have hy := (tendsto_const_nhds (x := x)).inner (𝕜 := ℂ) (tendsto_semigroupS hT hsv ht y)
  refine tendsto_nhds_unique hx ?_
  have heq : (fun n : ℕ => (inner ℂ (approxS hT n t x) y : ℂ))
      = fun n : ℕ => (inner ℂ x (approxS hT n t y) : ℂ) := by
    funext n
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (isSelfAdjoint_approxS hT n t)) x y
  rw [heq]
  exact hy
