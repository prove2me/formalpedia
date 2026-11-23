-- Prove2me | solution 1 for Csg.skirmishReachGoal_pre1_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:11:06.893366+00:00
-- url     : https://prove2.me/submissions/15a4944f-f008-49bf-b324-00fdf9f980c4

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_hide_hide_wait
import Theorems.Thm_Csg_skirmishK_support_hide_run_throw
import Theorems.Thm_Csg_skirmishK_support_home
import Theorems.Thm_Csg_skirmishK_support_wet


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.Pre1 ({SkirmishPos.home} : Set SkirmishPos) = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  obtain ⟨a1, ha1⟩ := hs
  cases s with
  | wet =>
      have h := ha1 SniperMove.wait
      rw [skirmishK_support_wet] at h
      exact absurd (Set.eq_of_mem_singleton (Set.singleton_subset_iff.mp h)) (by decide)
  | home =>
      have h := ha1 SniperMove.wait
      rw [skirmishK_support_home] at h
      exact absurd (Set.eq_of_mem_singleton (Set.singleton_subset_iff.mp h)) (by decide)
  | hide =>
      cases a1 with
      | hide =>
          have h := ha1 .wait
          rw [skirmishK_support_hide_hide_wait] at h
          exact absurd (Set.eq_of_mem_singleton (Set.singleton_subset_iff.mp h)) (by decide)
      | run =>
          have h := ha1 .throw
          rw [skirmishK_support_hide_run_throw] at h
          exact absurd (Set.eq_of_mem_singleton (Set.singleton_subset_iff.mp h)) (by decide)
end Csg
