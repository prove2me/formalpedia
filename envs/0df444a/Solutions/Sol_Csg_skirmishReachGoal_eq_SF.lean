-- Prove2me | solution 1 for Csg.skirmishReachGoal_eq_SF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:18.229802+00:00
-- url     : https://prove2.me/submissions/497bdcfc-591d-4ee1-82ab-90833bbe2685

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishReachGoal_pre1_empty
import Theorems.Thm_Csg_CSG_subset_SF


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.SF ({SkirmishPos.home} : Set SkirmishPos) = {SkirmishPos.home} := by
  have hfixed : skirmishCSG.SFOrderHom ({SkirmishPos.home} : Set SkirmishPos)
      ({SkirmishPos.home} : Set SkirmishPos) = {SkirmishPos.home} := by
    change skirmishCSG.Pre1 ({SkirmishPos.home} : Set SkirmishPos) ∪ {SkirmishPos.home}
        = ({SkirmishPos.home} : Set SkirmishPos)
    rw [skirmishReachGoal_pre1_empty, Set.empty_union]
  exact le_antisymm
    ((skirmishCSG.SFOrderHom {SkirmishPos.home}).lfp_le_fixed hfixed)
    (skirmishCSG.subset_SF {SkirmishPos.home})
end Csg
