-- Prove2me | solution 1 for Freiman.other22_represented_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:13:10.823002+00:00
-- url     : https://prove2.me/submissions/3a6816ae-9de7-4968-ae92-9bec1ad5bdce

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_lowerHistory_greater_semantics

open Freiman

theorem solution (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (u v : LowerPair) (a b : Bool) (x y : ℝ)
    (hx : other22EndpointRepresented base C u a x)
    (hy : other22EndpointRepresented base C v b y)
    (hh : ∀ z ∈ lowerHistoryComparisons C u v a b,
      lowerHistoryAtBase base z.1 → lowerHistoryComparisonHolds z.2 (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)) :
    y ≤ x := by
  obtain ⟨ex,cx,hx,hcx,hex,hxp⟩ := hx
  obtain ⟨ey,cy,hy,hcy,hey,hyp⟩ := hy
  have hmem : (cx++cy,lowerHistoryGreater C ex ey) ∈ lowerHistoryComparisons C u v a b := by
    apply List.mem_flatMap.mpr
    refine ⟨(ex,cx),hx,?_⟩
    exact List.mem_map.mpr ⟨(ey,cy),hy,rfl⟩
  have hcs : lowerHistoryAtBase base (cx++cy) := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hcx d hd
    · exact hcy d hd
  rw [hex,hey]
  exact (lowerHistory_greater_semantics base C hc ex ey hxp hyp).mp (hh _ hmem hcs)
