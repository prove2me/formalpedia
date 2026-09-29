-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u154664960_157286400_r119275520_125173760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:10:30.673948+00:00
-- url     : https://prove2.me/submissions/98dae958-cacc-48f7-b18c-41026c0950b0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [59/320, 3/16]`, `ρ ∈ [91/640, 191/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 154664960 155320320 119275520 120750080 ⟨⟨67366945832, 67366945838⟩, ⟨65441377801, 69307826671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 154664960 155320320 120750080 122224640 ⟨⟨68145546523, 68145546529⟩, ⟨66217276582, 70089123257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 155320320 155975680 119275520 120750080 ⟨⟨67072020413, 67072020415⟩, ⟨65152585896, 69006681787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 155320320 155975680 120750080 122224640 ⟨⟨67847582874, 67847582877⟩, ⟨65925453514, 69784933315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 154664960 155320320 122224640 123699200 ⟨⟨68923093125, 68923093132⟩, ⟨66992128369, 70869358612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154664960 155320320 123699200 125173760 ⟨⟨69699590059, 69699590066⟩, ⟨67765937544, 71648537194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 155320320 155975680 122224640 123699200 ⟨⟨68622103143, 68622103146⟩, ⟨66697285928, 70562135612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 155320320 155975680 123699200 125173760 ⟨⟨69395585566, 69395585569⟩, ⟨67468087447, 71338293067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 155975680 156631040 119275520 120750080 ⟨⟨66778636102, 66778636109⟩, ⟨64865290485, 68707123471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 155975680 156631040 120750080 122224640 ⟨⟨67551172071, 67551172079⟩, ⟨65635138684, 69482341665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 156631040 157286400 119275520 120750080 ⟨⟨66486777531, 66486777538⟩, ⟨64579476685, 68409135843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 156631040 157286400 120750080 122224640 ⟨⟨67256298661, 67256298667⟩, ⟨65346317123, 69181332348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 155975680 156631040 122224640 123699200 ⟨⟨68322677609, 68322677618⟩, ⟨66403963337, 70256522497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 155975680 156631040 123699200 125173760 ⟨⟨69093156995, 69093157003⟩, ⟨67171768683, 71029670282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 156631040 157286400 122224640 123699200 ⟨⟨68024800987, 68024800995⟩, ⟨66112145540, 69952503222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 156631040 157286400 123699200 125173760 ⟨⟨68792288725, 68792288731⟩, ⟨66876966113, 70722652713⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 154664960 157286400 119275520 125173760 t = true :=
  ⟨_, (join_su (m := 155975680) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 155320320) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 120750080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 155320320) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 123699200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 122224640) (by decide) (join_su (m := 156631040) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 120750080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 156631040) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 123699200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (59/320 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (191/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
