-- Prove2me | solution 1 for Csg.skirmish_wet_not_mem_Apre1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:08:21.249374+00:00
-- url     : https://prove2.me/submissions/9dd36122-4ab9-4200-9065-e724b0e808bd

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_wet


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (x y : Set SkirmishPos) (hx : SkirmishPos.wet ∉ x) :
    SkirmishPos.wet ∉ skirmishCSG.Apre1 x y := by
  intro hmem
  have heq : skirmishCSG.B (skirmishCSG.A ∅ y SkirmishPos.wet) x SkirmishPos.wet
      = (Set.univ : Set SniperMove) := hmem
  have hW : SniperMove.wait ∈
      skirmishCSG.B (skirmishCSG.A ∅ y SkirmishPos.wet) x SkirmishPos.wet := by
    rw [heq]; exact Set.mem_univ _
  obtain ⟨a1, _, y', hy'⟩ := hW
  rw [skirmishK_support_wet] at hy'
  have hyeq : y' = SkirmishPos.wet := Set.mem_singleton_iff.mp hy'.1
  rw [hyeq] at hy'
  exact hx hy'.2
end Csg
