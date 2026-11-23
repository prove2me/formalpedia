-- Prove2me | solution 1 for Csg.skirmish_hide_not_mem_G_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:02.793142+00:00
-- url     : https://prove2.me/submissions/a5621b2c-b265-4756-b8ea-86b660acbb01

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_CSG_G_subset
import Theorems.Thm_Csg_skirmishK_support_hide_hide_throw
import Theorems.Thm_Csg_skirmishK_support_hide_run_wait


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∉ skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos) := by
  intro hmem
  have hsub : skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos) ⊆ {SkirmishPos.hide} :=
    skirmishCSG.G_subset {SkirmishPos.hide}
  have h : skirmishCSG.GOrderHom ({SkirmishPos.hide} : Set SkirmishPos)
        (skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos))
      = skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos) :=
    (skirmishCSG.GOrderHom {SkirmishPos.hide}).map_gfp
  rw [← h] at hmem
  have hpre : SkirmishPos.hide ∈
      skirmishCSG.Pre1 (skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos)) := hmem.1
  have hpre' : SkirmishPos.hide ∈ skirmishCSG.Pre1 ({SkirmishPos.hide} : Set SkirmishPos) :=
    skirmishCSG.Pre1_mono hsub hpre
  obtain ⟨a1, ha1⟩ := hpre'
  cases a1 with
  | hide =>
      have hthrow := ha1 .throw
      rw [skirmishK_support_hide_hide_throw] at hthrow
      have hmemhide : SkirmishPos.home ∈ ({SkirmishPos.hide} : Set SkirmishPos) :=
        Set.singleton_subset_iff.mp hthrow
      exact absurd (Set.eq_of_mem_singleton hmemhide) (by decide)
  | run =>
      have hwait := ha1 .wait
      rw [skirmishK_support_hide_run_wait] at hwait
      have hmemhide : SkirmishPos.home ∈ ({SkirmishPos.hide} : Set SkirmishPos) :=
        Set.singleton_subset_iff.mp hwait
      exact absurd (Set.eq_of_mem_singleton hmemhide) (by decide)
end Csg
