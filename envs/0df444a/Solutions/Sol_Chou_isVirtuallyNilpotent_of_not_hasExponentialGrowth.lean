-- Prove2me | solution 1 for Chou.isVirtuallyNilpotent_of_not_hasExponentialGrowth
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-23T21:47:51.225417+00:00
-- url     : https://prove2.me/submissions/1a74b363-3d66-4fa8-a412-b18dfe1d0a48

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Theorems.Thm_Chou_hasExponentialGrowth_of_hasFreeSubsemigroupOfRankTwo
import Theorems.Thm_Rosenblatt_isPolycyclic_of_fg_of_isSolvable_of_not_hasFreeSubsemigroupOfRankTwo
import Theorems.Thm_Rosenblatt_isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isPolycyclic
import Mathlib

set_option autoImplicit false

open Chou

/-- A finitely generated solvable group without exponential growth is virtually nilpotent.
    Pure assembly over proved deps (D1 contrapositive, D2 polycyclic, D3 inclusive disjunction). -/
theorem solution {G : Type*} [Group G] [Group.FG G] [Group.IsSolvable G]
    (h : ¬ HasExponentialGrowth G) : Group.IsVirtuallyNilpotent G := by
  have hfree : ¬ HasFreeSubsemigroupOfRankTwo G := by
    intro hfs
    exact h (hasExponentialGrowth_of_hasFreeSubsemigroupOfRankTwo hfs)
  have hpoly : MilnorWolf.IsPolycyclic G :=
    Rosenblatt.isPolycyclic_of_fg_of_isSolvable_of_not_hasFreeSubsemigroupOfRankTwo hfree
  rcases Rosenblatt.isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isPolycyclic hpoly with hvn | hfs
  · exact hvn
  · exact absurd hfs hfree
