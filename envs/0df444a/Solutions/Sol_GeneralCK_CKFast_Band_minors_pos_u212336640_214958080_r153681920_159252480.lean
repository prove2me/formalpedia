-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:26:30.088804+00:00
-- url     : https://prove2.me/submissions/ef3e3d6e-de10-42cf-92b3-b678806c017c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 153681920 155074560 ⟨⟨58669552181, 58669552188⟩, ⟨57122851120, 60226166504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212336640 212992000 155074560 156467200 ⟨⟨59179143534, 59179143540⟩, ⟨57630497310, 60737707156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212992000 213647360 153681920 155074560 ⟨⟨58415857491, 58415857497⟩, ⟨56872728128, 59968862235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 155074560 156467200 ⟨⟨58923400734, 58923400740⟩, ⟨57378331261, 60478349779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 212992000 156467200 157859840 ⟨⟨59688418286, 59688418292⟩, ⟨58137828153, 61248929939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 212336640 212992000 157859840 159252480 ⟨⟨60197377295, 60197377301⟩, ⟨58644844501, 61759835711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212992000 213647360 156467200 157859840 ⟨⟨59430631117, 59430631124⟩, ⟨57883622762, 60987523220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212992000 213647360 157859840 159252480 ⟨⟨59937549485, 59937549490⟩, ⟨58388603468, 61496383404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 213647360 214302720 153681920 155074560 ⟨⟨58162998682, 58162998687⟩, ⟨56623421904, 59712413234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 213647360 214302720 155074560 156467200 ⟨⟨58668498742, 58668498749⟩, ⟨57126986902, 60219852602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214302720 214958080 153681920 155074560 ⟨⟨57910969221, 57910969226⟩, ⟨56374926069, 59456812809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 214302720 214958080 155074560 156467200 ⟨⟨58414430998, 58414431002⟩, ⟨56876457822, 59962208904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213647360 214302720 156467200 157859840 ⟨⟨59173689647, 59173689653⟩, ⟨57630243943, 60726981596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 213647360 214302720 157859840 159252480 ⟨⟨59678572225, 59678572231⟩, ⟨58133193853, 61233801049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 214302720 214958080 156467200 157859840 ⟨⟨58917587282, 58917587286⟩, ⟨57377685255, 60467298316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214302720 214958080 157859840 159252480 ⟨⟨59420438892, 59420438896⟩, ⟨57878609186, 60972081865⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 153681920 159252480 t = true :=
  ⟨_, (join_su (m := 213647360) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 212992000) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 155074560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212992000) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 157859840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 156467200) (by decide) (join_su (m := 214302720) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 155074560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 214302720) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 157859840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
