-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u154664960_155975680_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:02:15.724986+00:00
-- url     : https://prove2.me/submissions/122cded9-b32e-4a53-9615-31f4b5c580a7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [59/320, 119/640]`, `ρ ∈ [1/10, 137/1280]` by 15 cells of the computing
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
theorem cell0 : cellOK 154664960 154992640 83886080 85360640 ⟨⟨48407146465, 48407146468⟩, ⟨47240838710, 49579593489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 154992640 155320320 83886080 85360640 ⟨⟨48297717184, 48297717191⟩, ⟨47133493318, 49468060311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 154664960 154992640 85360640 86835200 ⟨⟨49213272740, 49213272743⟩, ⟨48045312892, 50387367897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 154992640 155320320 85360640 86835200 ⟨⟨49102166438, 49102166446⟩, ⟨47936293511, 50274154720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 155320320 155648000 83886080 85360640 ⟨⟨48188594328, 48188594335⟩, ⟨47026446788, 49356841220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 155648000 155975680 83886080 85360640 ⟨⟨48079776280, 48079776286⟩, ⟨46919697546, 49245934560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 155320320 155648000 85360640 86835200 ⟨⟨48991370418, 48991370424⟩, ⟨47827576846, 50161259492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 155648000 155975680 85360640 86835200 ⟨⟨48880883047, 48880883053⟩, ⟨47719161303, 50048680540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 154664960 154992640 86835200 88309760 ⟨⟨50018228056, 50018228059⟩, ⟨48848621589, 51193965856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 154992640 155320320 86835200 88309760 ⟨⟨49905451653, 49905451659⟩, ⟨48737935096, 51079079644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 155320320 88309760 89784320 ⟨⟨50764757805, 50764757811⟩, ⟨48897640097, 52647302709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 155320320 155648000 86835200 88309760 ⟨⟨49792989347, 49792989353⟩, ⟨48627555130, 50964515201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 155648000 155975680 86835200 88309760 ⟨⟨49680839491, 49680839498⟩, ⟨48517480082, 50850270836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 155320320 155648000 88309760 89784320 ⟨⟨50593456077, 50593456083⟩, ⟨49426386569, 51766613336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 155648000 155975680 88309760 89784320 ⟨⟨50479650529, 50479650537⟩, ⟨49314658771, 51650710397⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 154664960 155975680 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 155320320) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 154992640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 154992640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 155648000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 155648000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 155320320) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 154992640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 88309760) (by decide) (join_su (m := 155648000) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 155648000) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (59/320 : ℝ) (119/640 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e1 : (((155975680 : ℤ) : ℝ) / (D : ℝ)) = (119/640 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
