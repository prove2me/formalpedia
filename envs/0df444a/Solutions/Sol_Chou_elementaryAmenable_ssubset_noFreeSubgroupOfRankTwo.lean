-- Prove2me | solution 1 for Chou.elementaryAmenable_ssubset_noFreeSubgroupOfRankTwo
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T23:05:57.053914+00:00
-- url     : https://prove2.me/submissions/7dbf2161-2325-44d6-8cfb-6b6787d95650

import Definitions.Def_Chou_Classes
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Growth
import Theorems.Thm_Garrido_isAmenable_of_elementaryAmenable
import Theorems.Thm_Garrido_noFreeSubgroupOfRankTwo_of_isAmenable
import Theorems.Thm_Chou_exists_noFreeSubgroupOfRankTwo_not_elementaryAmenable
import Mathlib

universe u

section
section

namespace Chou

theorem elementaryAmenable_ssubset_noFreeSubgroupOfRankTwo :
    (∀ (G : Type u) [Group G], ElementaryAmenable G → NoFreeSubgroupOfRankTwo G) ∧
      ∃ (G : Type) (_ : Group G), NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G :=
  ⟨fun _ _ hG => Garrido.noFreeSubgroupOfRankTwo_of_isAmenable
      (Garrido.isAmenable_of_elementaryAmenable hG),
    exists_noFreeSubgroupOfRankTwo_not_elementaryAmenable⟩

end Chou

end
end

section
open Chou

theorem solution :
    (∀ (G : Type u) [Group G], ElementaryAmenable G → NoFreeSubgroupOfRankTwo G) ∧
      ∃ (G : Type) (_ : Group G), NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G := by
  apply Chou.elementaryAmenable_ssubset_noFreeSubgroupOfRankTwo <;> assumption

end
