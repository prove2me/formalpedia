-- Prove2me | solution 1 for Freiman.lowerHistory_join_bindings
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-11T02:24:23.41826+00:00
-- url     : https://prove2.me/submissions/a79f5eb6-d97c-4dd8-9e71-a0bed83181b9

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option autoImplicit false

theorem solution (hs : lowerHistoryPaths.size = 1492 ∧ lowerHistoryWitnesses.size = 1194 ∧ lowerHistoryRecords.size = 3624) (h0 : lowerHistoryBindingBatch 0 50) (h1 : lowerHistoryBindingBatch 50 100) (h2 : lowerHistoryBindingBatch 100 150) (h3 : lowerHistoryBindingBatch 150 200) (h4 : lowerHistoryBindingBatch 200 250) (h5 : lowerHistoryBindingBatch 250 300) (h6 : lowerHistoryBindingBatch 300 350) (h7 : lowerHistoryBindingBatch 350 400) (h8 : lowerHistoryBindingBatch 400 450) (h9 : lowerHistoryBindingBatch 450 500) (h10 : lowerHistoryBindingBatch 500 550) (h11 : lowerHistoryBindingBatch 550 600) (h12 : lowerHistoryBindingBatch 600 650) (h13 : lowerHistoryBindingBatch 650 700) (h14 : lowerHistoryBindingBatch 700 750) (h15 : lowerHistoryBindingBatch 750 800) (h16 : lowerHistoryBindingBatch 800 850) (h17 : lowerHistoryBindingBatch 850 900) (h18 : lowerHistoryBindingBatch 900 950) (h19 : lowerHistoryBindingBatch 950 1000) (h20 : lowerHistoryBindingBatch 1000 1050) (h21 : lowerHistoryBindingBatch 1050 1100) (h22 : lowerHistoryBindingBatch 1100 1150) (h23 : lowerHistoryBindingBatch 1150 1200) (h24 : lowerHistoryBindingBatch 1200 1250) (h25 : lowerHistoryBindingBatch 1250 1300) (h26 : lowerHistoryBindingBatch 1300 1350) (h27 : lowerHistoryBindingBatch 1350 1400) (h28 : lowerHistoryBindingBatch 1400 1450) (h29 : lowerHistoryBindingBatch 1450 1492) :
    lowerHistoryAllBindings := by
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  have hget : lowerHistoryPaths[i]? = some p := by
    simpa only [Array.getElem?_toList] using hi
  obtain ⟨hbound, _⟩ := Array.getElem?_eq_some_iff.mp hget
  have hlast : i < 1492 := by
    simpa only [hs.1] using hbound
  by_cases hi50 : i < 50
  · exact h0 i (Nat.zero_le i) hi50 p hget
  by_cases hi100 : i < 100
  · exact h1 i (by omega) hi100 p hget
  by_cases hi150 : i < 150
  · exact h2 i (by omega) hi150 p hget
  by_cases hi200 : i < 200
  · exact h3 i (by omega) hi200 p hget
  by_cases hi250 : i < 250
  · exact h4 i (by omega) hi250 p hget
  by_cases hi300 : i < 300
  · exact h5 i (by omega) hi300 p hget
  by_cases hi350 : i < 350
  · exact h6 i (by omega) hi350 p hget
  by_cases hi400 : i < 400
  · exact h7 i (by omega) hi400 p hget
  by_cases hi450 : i < 450
  · exact h8 i (by omega) hi450 p hget
  by_cases hi500 : i < 500
  · exact h9 i (by omega) hi500 p hget
  by_cases hi550 : i < 550
  · exact h10 i (by omega) hi550 p hget
  by_cases hi600 : i < 600
  · exact h11 i (by omega) hi600 p hget
  by_cases hi650 : i < 650
  · exact h12 i (by omega) hi650 p hget
  by_cases hi700 : i < 700
  · exact h13 i (by omega) hi700 p hget
  by_cases hi750 : i < 750
  · exact h14 i (by omega) hi750 p hget
  by_cases hi800 : i < 800
  · exact h15 i (by omega) hi800 p hget
  by_cases hi850 : i < 850
  · exact h16 i (by omega) hi850 p hget
  by_cases hi900 : i < 900
  · exact h17 i (by omega) hi900 p hget
  by_cases hi950 : i < 950
  · exact h18 i (by omega) hi950 p hget
  by_cases hi1000 : i < 1000
  · exact h19 i (by omega) hi1000 p hget
  by_cases hi1050 : i < 1050
  · exact h20 i (by omega) hi1050 p hget
  by_cases hi1100 : i < 1100
  · exact h21 i (by omega) hi1100 p hget
  by_cases hi1150 : i < 1150
  · exact h22 i (by omega) hi1150 p hget
  by_cases hi1200 : i < 1200
  · exact h23 i (by omega) hi1200 p hget
  by_cases hi1250 : i < 1250
  · exact h24 i (by omega) hi1250 p hget
  by_cases hi1300 : i < 1300
  · exact h25 i (by omega) hi1300 p hget
  by_cases hi1350 : i < 1350
  · exact h26 i (by omega) hi1350 p hget
  by_cases hi1400 : i < 1400
  · exact h27 i (by omega) hi1400 p hget
  by_cases hi1450 : i < 1450
  · exact h28 i (by omega) hi1450 p hget
  exact h29 i (by omega) hlast p hget

#print axioms solution
