-- Prove2me | solution 1 for BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T15:08:33.612861+00:00
-- url     : https://prove2.me/submissions/a9536330-6681-4912-b558-b36df8ce7577

-- Generated from ChapterNonnegSemigroup.lean — solution of BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le
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
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) (m : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖semigroupS hT hsv ht h - approxS hT m t h‖ ≤ t * ‖k - yosidaAt hT m h‖ := by

  have hf : Tendsto (fun n : ℕ => ‖approxS hT n t h - approxS hT m t h‖) atTop
      (𝓝 ‖semigroupS hT hsv ht h - approxS hT m t h‖) :=
    ((tendsto_semigroupS hT hsv ht h).sub tendsto_const_nhds).norm
  have hg : Tendsto (fun n : ℕ => t * ‖yosidaAt hT n h - yosidaAt hT m h‖) atTop
      (𝓝 (t * ‖k - yosidaAt hT m h‖)) :=
    (((tendsto_yosidaAt hT hsv hk).sub tendsto_const_nhds).norm).const_mul t
  exact le_of_tendsto_of_tendsto' hf hg (fun n => norm_approxS_sub_apply_le hT n m ht h)
