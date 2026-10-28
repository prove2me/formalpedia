-- Prove2me | solution 1 for BookProof.NonnegSemigroup.norm_semigroupS_sub_self_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T15:08:34.791901+00:00
-- url     : https://prove2.me/submissions/0e1f58e4-681d-4b8b-8636-fb48765a5f5c

-- Generated from ChapterNonnegSemigroup.lean — solution of BookProof.NonnegSemigroup.norm_semigroupS_sub_self_le_of_mem
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup
import Theorems.Thm_BookProof_NonnegSemigroup_norm_expNeg_sub_self_le
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
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) {t : ℝ} (ht : 0 ≤ t) :
    ‖semigroupS hT hsv ht h - h‖ ≤ t * ‖k‖ := by

  have hf : Tendsto (fun n : ℕ => ‖approxS hT n t h - h‖) atTop
      (𝓝 ‖semigroupS hT hsv ht h - h‖) :=
    ((tendsto_semigroupS hT hsv ht h).sub tendsto_const_nhds).norm
  have hg : Tendsto (fun n : ℕ => t * ‖yosidaAt hT n h‖) atTop (𝓝 (t * ‖k‖)) :=
    (((tendsto_yosidaAt hT hsv hk)).norm).const_mul t
  refine le_of_tendsto_of_tendsto' hf hg (fun n => ?_)
  exact norm_expNeg_sub_self_le _ (yosidaAt_nonneg hT n) ht h
