-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_230686720_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:35:25.998496+00:00
-- url     : https://prove2.me/submissions/07b1f145-752e-4bef-8f52-67a208738c8d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 11/40]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 228065280 228720640 237240320 240025600 ⟨⟨80328198113, 80328198120⟩, ⟨78479305670, 82190420357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228720640 229376000 237240320 240025600 ⟨⟨79980587243, 79980587250⟩, ⟨78136469772, 81837984376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228065280 228720640 240025600 242810880 ⟨⟨81224866227, 81224866234⟩, ⟨79372116259, 83090952690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228720640 229376000 240025600 242810880 ⟨⟨80873704416, 80873704423⟩, ⟨79025738476, 82734956865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 229376000 230031360 237240320 240025600 ⟨⟨79633878099, 79633878106⟩, ⟨77794514626, 81486471390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230031360 230686720 237240320 240025600 ⟨⟨79288064285, 79288064292⟩, ⟨77453433987, 81135874855⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 229376000 230031360 240025600 242810880 ⟨⟨80523449607, 80523449613⟩, ⟨78680246732, 82379889296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230031360 230686720 240025600 242810880 ⟨⟨80174095378, 80174095386⟩, ⟨78335634762, 82025743414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 228720640 242810880 245596160 ⟨⟨82120723163, 82120723170⟩, ⟨80264119206, 83990670240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228720640 229376000 242810880 245596160 ⟨⟨81766020036, 81766020042⟩, ⟨79914209078, 83631124278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 228720640 245596160 248381440 ⟨⟨83015773021, 83015773027⟩, ⟨81155318590, 84889577129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228720640 229376000 245596160 248381440 ⟨⟨82657538140, 82657538145⟩, ⟨80801885600, 84526490677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 229376000 230031360 242810880 245596160 ⟨⟨81412229092, 81412229099⟩, ⟨79565190190, 83272511741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 230031360 230686720 242810880 245596160 ⟨⟨81059343893, 81059343899⟩, ⟨79217056248, 82914826035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230031360 245596160 248381440 ⟨⟨82300220537, 82300220543⟩, ⟨80449348959, 84164342724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230031360 230686720 245596160 248381440 ⟨⟨81943813748, 81943813754⟩, ⟨80097702349, 83803126657⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 230686720 237240320 248381440 t = true :=
  ⟨_, (join_sr (m := 242810880) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 240025600) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 228720640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 240025600) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 230031360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 229376000) (by decide) (join_sr (m := 245596160) (by decide) (join_su (m := 228720640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 228720640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 245596160) (by decide) (join_su (m := 230031360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 230031360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
