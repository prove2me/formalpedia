-- Prove2me | solution 1 for Eden.finiteTimeDimension_attractor_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:18.192572+00:00
-- url     : https://prove2.me/submissions/88ae292c-1f2e-4685-b418-e2ed471fb481

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_finiteTimeDimension_le_target
import Theorems.Thm_Eden_finiteTimeDimension_eq_target_iff
import Theorems.Thm_Eden_torus_nonempty
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    IsGreatest (finiteTimeDimension c t '' attractor) (targetDimension c) := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_attractor hp,
      (finiteTimeDimension_eq_target_iff hc ht (torus_subset_attractor hp)).2 hp⟩
  · rintro d ⟨p, hp, rfl⟩
    exact finiteTimeDimension_le_target hc ht hp
end Eden
