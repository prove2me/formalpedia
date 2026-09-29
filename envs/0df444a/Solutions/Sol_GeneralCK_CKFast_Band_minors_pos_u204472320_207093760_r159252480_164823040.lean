-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_207093760_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:11.948543+00:00
-- url     : https://prove2.me/submissions/bc57ebae-2376-45e2-b627-4c293bd9cc9e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 79/320]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205127680 159252480 160645120 ⟨⟨63917625471, 63917625473⟩, ⟨62318499140, 65527155364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 204472320 205127680 160645120 162037760 ⟨⟨64450737518, 64450737521⟩, ⟨62849611295, 66062270659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 205127680 205783040 159252480 160645120 ⟨⟨63644954008, 63644954013⟩, ⟨62049661715, 65250608776⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205127680 205783040 160645120 162037760 ⟨⟨64175973207, 64175973213⟩, ⟨62578686021, 65783626287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 205127680 162037760 163430400 ⟨⟨64983489074, 64983489077⟩, ⟨63380364538, 66597023858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 204472320 205127680 163430400 164823040 ⟨⟨65515881158, 65515881161⟩, ⟨63910759885, 67131415992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205127680 205783040 162037760 163430400 ⟨⟨64706636081, 64706636088⟩, ⟨63107355551, 66316285903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 205127680 205783040 163430400 164823040 ⟨⟨65236943633, 65236943640⟩, ⟨63635671304, 66848588631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 205783040 206438400 159252480 160645120 ⟨⟨63373222830, 63373222836⟩, ⟨61781743453, 64975023892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205783040 206438400 160645120 162037760 ⟨⟨63902154317, 63902154324⟩, ⟨62308685042, 65505948759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 206438400 207093760 159252480 160645120 ⟨⟨63102424483, 63102424488⟩, ⟨61514737076, 64700393081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 206438400 207093760 160645120 162037760 ⟨⟨63629273361, 63629273367⟩, ⟨62039601047, 65229230412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 205783040 206438400 162037760 163430400 ⟨⟨64430733602, 64430733609⟩, ⟨62835275948, 66036519885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 205783040 206438400 163430400 164823040 ⟨⟨64958961674, 64958961680⟩, ⟨63361517157, 66566738262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 206438400 207093760 162037760 163430400 ⟨⟨64155774119, 64155774126⟩, ⟨62564118389, 65757718111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 206438400 207093760 163430400 164823040 ⟨⟨64681927732, 64681927738⟩, ⟨63088290070, 66285857160⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 207093760 159252480 164823040 t = true :=
  ⟨_, (join_su (m := 205783040) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 205127680) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 160645120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 205127680) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163430400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 162037760) (by decide) (join_su (m := 206438400) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 160645120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 206438400) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163430400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (79/320 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
