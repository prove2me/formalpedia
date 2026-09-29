-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_compare_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:37:07.916985+00:00
-- url     : https://prove2.me/submissions/77a8f93d-a576-432e-b9c0-78dfda6b95f7

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem solution (he : LowerEarlyTerminalEndpointLaw) (hg : LowerEarlyTerminalGreaterLaw)
    (C : LowerEarlyTerminalCatalog) (p : LowerPair) (hm : lowerEarlyTerminalMatches p C)
    (u v : LowerPair) (hi hj strict : Bool)
    (h : ∀ b ∈ lowerEarlyTerminalCompare C u hi v hj strict, lowerEarlyTerminalAt p b.1 →
      section14ComparisonHolds b.2 (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)) :
    lowerEarlyTerminalKindHolds p (.compare u hi v hj strict) := by
  obtain ⟨zu, csu, hzu, hcu, hpu, heu⟩ := he (lowerNormalize p) (lowerEarlyTerminalContext C) rfl hm u hi
  obtain ⟨zv, csv, hzv, hcv, hpv, hev⟩ := he (lowerNormalize p) (lowerEarlyTerminalContext C) rfl hm v hj
  have hmem : (csu ++ csv, lowerEarlyTerminalGreater zu zv strict) ∈ lowerEarlyTerminalCompare C u hi v hj strict :=
    List.mem_flatMap.2 ⟨(zu, csu), hzu, List.mem_map.2 ⟨(zv, csv), hzv, rfl⟩⟩
  have hat : lowerEarlyTerminalAt p (csu ++ csv) := by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hcu b hb
    · exact hcv b hb
  have hh := h _ hmem hat
  have hiff := hg (lowerNormalize p) (lowerEarlyTerminalContext C) rfl hm zu zv strict hpu hpv
  have hcmp := hiff.1 hh
  have eu : lowerEarlyTerminalEndpoint p u hi =
      lowerHistoryValue (lowerNormalize p) (lowerEarlyTerminalContext C) zu := heu
  have ev : lowerEarlyTerminalEndpoint p v hj =
      lowerHistoryValue (lowerNormalize p) (lowerEarlyTerminalContext C) zv := hev
  show (if strict then lowerEarlyTerminalEndpoint p v hj < lowerEarlyTerminalEndpoint p u hi
    else lowerEarlyTerminalEndpoint p v hj ≤ lowerEarlyTerminalEndpoint p u hi)
  rw [eu, ev]
  exact hcmp
