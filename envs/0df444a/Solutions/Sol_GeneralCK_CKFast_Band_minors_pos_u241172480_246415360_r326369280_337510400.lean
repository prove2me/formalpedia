-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r326369280_337510400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:49:15.58731+00:00
-- url     : https://prove2.me/submissions/23da26bb-416b-4f81-b54c-c9e5f3642b4e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [249/640, 103/256]` by 16 cells of the computing
correction-band checker; each cell is kernel-checked in its own declaration. -/

theorem leaf_ok {U0 U1 R0 R1 : ℤ} {h : Hint} (hc : cellOK U0 U1 R0 R1 h = true) :
    treeOK U0 U1 R0 R1 (.leaf h) = true := by
  simpa only [treeOK] using hc

theorem join_su {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (U0 ≤ m) && decide (m ≤ U1)) = true)
    (hl : treeOK U0 m R0 R1 l = true) (hr : treeOK m U1 R0 R1 r = true) :
    treeOK U0 U1 R0 R1 (.su m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

theorem join_sr {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (R0 ≤ m) && decide (m ≤ R1)) = true)
    (hl : treeOK U0 U1 R0 m l = true) (hr : treeOK U0 U1 m R1 r = true) :
    treeOK U0 U1 R0 R1 (.sr m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

set_option maxRecDepth 100000 in
theorem cell0 : cellOK 241172480 242483200 326369280 329154560 ⟨⟨99472972502, 99472972509⟩, ⟨96247946836, 102734421269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 242483200 329154560 331939840 ⟨⟨100279109841, 100279109848⟩, ⟨97047330199, 103547348913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 243793920 326369280 329154560 ⟨⟨98599928749, 98599928755⟩, ⟨95388155382, 101847936134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 329154560 331939840 ⟨⟨99399635485, 99399635492⟩, ⟨96181133107, 102654408901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 242483200 331939840 334725120 ⟨⟨101084706981, 101084706988⟩, ⟨97846175254, 104359734296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 242483200 334725120 337510400 ⟨⟨101889766608, 101889766616⟩, ⟨98644484670, 105171580118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243793920 331939840 334725120 ⟨⟨100198815038, 100198815045⟩, ⟨96973585363, 103460352598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242483200 243793920 334725120 337510400 ⟨⟨100997470016, 100997470022⟩, ⟨97765514745, 104265769849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 245104640 326369280 329154560 ⟨⟨97730452868, 97730452874⟩, ⟨94531826117, 100965126443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 243793920 245104640 329154560 331939840 ⟨⟨98523739389, 98523739395⟩, ⟨95318408764, 101765154523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 246415360 326369280 329154560 ⟨⟨96864497825, 96864497828⟩, ⟨93678913318, 100085943814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245104640 246415360 329154560 331939840 ⟨⟨97651374462, 97651374464⟩, ⟨94459111390, 100879537353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 331939840 334725120 ⟨⟨99316511503, 99316511510⟩, ⟨96104478550, 102564666488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243793920 245104640 334725120 337510400 ⟨⟨100108771743, 100108771751⟩, ⟨96890037994, 103363664880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 246415360 331939840 334725120 ⟨⟨98437749234, 98437749237⟩, ⟨95238808976, 101672627491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 334725120 337510400 ⟨⟨99223624604, 99223624607⟩, ⟨96018008526, 102465216697⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 326369280 337510400 t = true :=
  ⟨_, (join_su (m := 243793920) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 329154560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 242483200) (by decide) (join_sr (m := 334725120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 334725120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 331939840) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 329154560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245104640) (by decide) (join_sr (m := 334725120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 334725120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (103/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
