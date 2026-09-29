-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_228065280_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:26:44.587766+00:00
-- url     : https://prove2.me/submissions/9cb3dad3-8145-4201-b460-59fcdc60a7b5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 87/320]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226099200 226099200 228884480 ⟨⟨78075494396, 78075494403⟩, ⟨76222902882, 79941594347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226099200 226754560 226099200 228884480 ⟨⟨77738602039, 77738602046⟩, ⟨75890834058, 79599826459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226099200 228884480 231669760 ⟨⟨78989865809, 78989865816⟩, ⟨77133364972, 80859881428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226099200 226754560 228884480 231669760 ⟨⟨78649360533, 78649360540⟩, ⟨76797692575, 80514491433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 226754560 227409920 226099200 228884480 ⟨⟨77402615056, 77402615063⟩, ⟨75559648972, 79258985900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 227409920 228065280 226099200 228884480 ⟨⟨77067526950, 77067526953⟩, ⟨75229341281, 78919066012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 227409920 228884480 231669760 ⟨⟨78309766389, 78309766395⟩, ⟨76462909685, 80170034512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227409920 228065280 228884480 231669760 ⟨⟨77971076852, 77971076855⟩, ⟨76129009930, 79826503980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226099200 231669760 234455040 ⟨⟨79903369024, 79903369030⟩, ⟨78042962828, 81777296275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226099200 226754560 231669760 234455040 ⟨⟨79559261087, 79559261092⟩, ⟨77703697028, 81428294520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226099200 234455040 237240320 ⟨⟨80816008469, 80816008475⟩, ⟨78951700857, 82693843338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226099200 226754560 234455040 237240320 ⟨⟨80468308060, 80468308067⟩, ⟨78608851755, 82341240103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226754560 227409920 231669760 234455040 ⟨⟨79216069939, 79216069945⟩, ⟨77365326405, 81080231484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 227409920 228065280 231669760 234455040 ⟨⟨78873789035, 78873789037⟩, ⟨77027844563, 80733100456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 226754560 227409920 234455040 237240320 ⟨⟨80121530006, 80121530013⟩, ⟨78266903408, 81989581135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227409920 228065280 234455040 237240320 ⟨⟨79775667731, 79775667734⟩, ⟨77925849395, 81638859696⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 228065280 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226099200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 227409920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 226754560) (by decide) (join_sr (m := 234455040) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226099200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 234455040) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 227409920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
