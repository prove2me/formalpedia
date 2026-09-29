-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_167772160_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:47:27.996048+00:00
-- url     : https://prove2.me/submissions/5ea1242c-a3ce-4534-a9ed-6b6fe8a5aee1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 1/5]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 165150720 165806080 154664960 157614080 ⟨⟨80497083743, 80497083747⟩, ⟨78156069872, 82859721183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165806080 166461440 154664960 157614080 ⟨⟨80157748082, 80157748088⟩, ⟨77824546630, 82512453678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165150720 165806080 157614080 160563200 ⟨⟨81917819484, 81917819489⟩, ⟨79571308905, 84285929303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165806080 166461440 157614080 160563200 ⟨⟨81573229332, 81573229339⟩, ⟨79234543293, 83933395862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 166461440 167116800 154664960 157614080 ⟨⟨79819955910, 79819955918⟩, ⟨77494516927, 82166780658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167116800 167772160 154664960 157614080 ⟨⟨79483693199, 79483693205⟩, ⟨77165967235, 81822687576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 166461440 167116800 157614080 160563200 ⟨⟨81230198564, 81230198572⟩, ⟨78899287179, 83582472724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 167116800 167772160 157614080 160563200 ⟨⟨80888713057, 80888713065⟩, ⟨78565526934, 83233145254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 165150720 165806080 160563200 163512320 ⟨⟨83335369084, 83335369089⟩, ⟨80983387904, 85708924999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165806080 166461440 160563200 163512320 ⟨⟨82985559114, 82985559122⟩, ⟨80641414223, 85351160665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 165806080 163512320 166461440 ⟨⟨84749756790, 84749756795⟩, ⟨82392330853, 87128732781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 165806080 166461440 163512320 166461440 ⟨⟨84394761308, 84394761316⟩, ⟨82045183045, 86765772227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 166461440 167116800 160563200 163512320 ⟨⟨82637324067, 82637324073⟩, ⟨80300965646, 84995022093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 167116800 167772160 160563200 163512320 ⟨⟨82290649727, 82290649734⟩, ⟨79962028453, 84640494561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 166461440 167116800 163512320 166461440 ⟨⟨84041355936, 84041355942⟩, ⟨81699575597, 86404452540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 167116800 167772160 163512320 166461440 ⟨⟨83689526372, 83689526378⟩, ⟨81355494704, 86044758911⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 167772160 154664960 166461440 t = true :=
  ⟨_, (join_sr (m := 160563200) (by decide) (join_su (m := 166461440) (by decide) (join_sr (m := 157614080) (by decide) (join_su (m := 165806080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 165806080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 157614080) (by decide) (join_su (m := 167116800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 167116800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 166461440) (by decide) (join_sr (m := 163512320) (by decide) (join_su (m := 165806080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 165806080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163512320) (by decide) (join_su (m := 167116800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 167116800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
