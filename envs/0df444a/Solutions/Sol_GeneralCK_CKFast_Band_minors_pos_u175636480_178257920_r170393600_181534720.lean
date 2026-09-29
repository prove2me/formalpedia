-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u175636480_178257920_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:30.102756+00:00
-- url     : https://prove2.me/submissions/05ca2201-9f67-4877-b2a7-20ce1a39726e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [67/320, 17/80]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 175636480 176291840 170393600 173178880 ⟨⟨82316672665, 82316672671⟩, ⟨80113251419, 84539026560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 176291840 176947200 170393600 173178880 ⟨⟨81974182422, 81974182429⟩, ⟨79777672849, 84189528512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 175636480 176291840 173178880 175964160 ⟨⟨83567711576, 83567711583⟩, ⟨81359444208, 85794898382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 176291840 176947200 173178880 175964160 ⟨⟨83220632117, 83220632125⟩, ⟨81019286916, 85440801092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 176947200 177602560 170393600 173178880 ⟨⟨81633102948, 81633102954⟩, ⟨79443463782, 83841483274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 177602560 178257920 170393600 173178880 ⟨⟨81293422151, 81293422158⟩, ⟨79110612519, 83494878361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 176947200 177602560 173178880 175964160 ⟨⟨82874975624, 82874975630⟩, ⟨80680511371, 85088168755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 177602560 178257920 173178880 175964160 ⟨⟨82530729939, 82530729947⟩, ⟨80343105806, 84736988821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 175636480 176291840 175964160 178749440 ⟨⟨84816454539, 84816454545⟩, ⟨82603358131, 87048457035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 176291840 176947200 175964160 178749440 ⟨⟨84464810784, 84464810790⟩, ⟨82258646786, 86689785671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 176291840 178749440 181534720 ⟨⟨86062916900, 86062916908⟩, ⟨83845008387, 88299718011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 176291840 176947200 178749440 181534720 ⟨⟨85706733542, 85706733548⟩, ⟨83495767437, 87936497514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 176947200 177602560 175964160 178749440 ⟨⟨84114601944, 84114601951⟩, ⟨81915329190, 86332591154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 177602560 178257920 175964160 178749440 ⟨⟨83765815799, 83765815806⟩, ⟨81573393507, 85976860871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 176947200 177602560 178749440 181534720 ⟨⟨85351996803, 85351996809⟩, ⟨83147931994, 87574765509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 177602560 178257920 178749440 181534720 ⟨⟨84998694403, 84998694409⟩, ⟨82801490157, 87214509325⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 175636480 178257920 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 176947200) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 176291840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 176291840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 177602560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 177602560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 176947200) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 176291840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 176291840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 177602560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 177602560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (67/320 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
