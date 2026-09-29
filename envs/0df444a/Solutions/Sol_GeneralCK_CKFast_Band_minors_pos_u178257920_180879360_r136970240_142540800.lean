-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_180879360_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:25:56.231546+00:00
-- url     : https://prove2.me/submissions/2dcca810-ff0e-4336-8fa2-c46d7ceb954c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 69/320]`, `ρ ∈ [209/1280, 87/512]` by 13 cells of the computing
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
theorem cell0 : cellOK 178257920 178913280 136970240 138362880 ⟨⟨65669784424, 65669784427⟩, ⟨63933330150, 67418572915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 178913280 138362880 139755520 ⟨⟨66300530062, 66300530064⟩, ⟨64561823473, 68051571050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178913280 179568640 136970240 138362880 ⟨⟨65390519718, 65390519725⟩, ⟨63658828608, 67134487044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 178913280 179568640 138362880 139755520 ⟨⟨66018835765, 66018835771⟩, ⟨64284898101, 67765049947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 178913280 139755520 142540800 ⟨⟨67245527938, 67245527941⟩, ⟨65123452016, 69386272450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178913280 179568640 139755520 142540800 ⟨⟨66960201849, 66960201855⟩, ⟨64844740893, 69094233552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180224000 136970240 138362880 ⟨⟨65112451452, 65112451458⟩, ⟨63385493341, 66851628264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 179568640 180224000 138362880 139755520 ⟨⟨65738345502, 65738345508⟩, ⟨64009146595, 67479763529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180224000 180879360 136970240 138362880 ⟨⟨64835569067, 64835569074⟩, ⟨63113314077, 66569985727⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180224000 180879360 138362880 139755520 ⟨⟨65459048667, 65459048673⟩, ⟨63734558637, 67195700901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 179568640 180224000 139755520 142540800 ⟨⟨66676091054, 66676091060⟩, ⟨64567205070, 68803450761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 180224000 180879360 139755520 141148160 ⟨⟨66081950247, 66081950253⟩, ⟨64355228379, 67820834821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180224000 180879360 141148160 142540800 ⟨⟨66704275708, 66704275715⟩, ⟨64975325193, 68445389404⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 180879360 136970240 142540800 t = true :=
  ⟨_, (join_su (m := 179568640) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 178913280) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 138362880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 178913280) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 139755520) (by decide) (join_su (m := 180224000) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 138362880) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 180224000) (by decide) (leaf_ok cell10) (join_sr (m := 141148160) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (69/320 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
