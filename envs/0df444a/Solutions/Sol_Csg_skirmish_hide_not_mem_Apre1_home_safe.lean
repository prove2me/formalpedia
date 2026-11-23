-- Prove2me | solution 1 for Csg.skirmish_hide_not_mem_Apre1_home_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:11:12.54809+00:00
-- url     : https://prove2.me/submissions/607597c4-8a33-4509-bc30-dd0d20c03338

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_hide_hide_wait
import Theorems.Thm_Csg_skirmishK_support_hide_run_throw


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∉ skirmishCSG.Apre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by
  intro hmem
  have hrun_not_mem : SoldierMove.run ∉ skirmishCSG.A ∅ skirmishSafe SkirmishPos.hide := by
    intro hrun
    rcases hrun SniperMove.throw with h | h
    · exact h
    · rw [skirmishK_support_hide_run_throw] at h
      exact absurd (Set.singleton_subset_iff.mp h) (by decide)
  have heq : skirmishCSG.B (skirmishCSG.A ∅ skirmishSafe SkirmishPos.hide)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide
      = (Set.univ : Set SniperMove) := hmem
  have hW : SniperMove.wait ∈ skirmishCSG.B (skirmishCSG.A ∅ skirmishSafe SkirmishPos.hide)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide := by
    rw [heq]; exact Set.mem_univ _
  obtain ⟨a1, ha1, y', hy'⟩ := hW
  cases a1 with
  | run => exact hrun_not_mem ha1
  | hide =>
      rw [skirmishK_support_hide_hide_wait] at hy'
      have hyeq : y' = SkirmishPos.hide := Set.mem_singleton_iff.mp hy'.1
      rw [hyeq] at hy'
      exact absurd (Set.eq_of_mem_singleton hy'.2) (by decide)
end Csg
