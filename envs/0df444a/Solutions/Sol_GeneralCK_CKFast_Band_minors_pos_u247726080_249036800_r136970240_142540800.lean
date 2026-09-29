-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u247726080_249036800_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:51:26.649163+00:00
-- url     : https://prove2.me/submissions/2881dc14-44e4-4852-b5a7-89e00e5da301

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [189/640, 19/64]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 247726080 248053760 136970240 138362880 ⟨⟨41193114791, 41193114798⟩, ⟨40399549889, 41989567076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 248053760 248381440 136970240 138362880 ⟨⟨41095695565, 41095695568⟩, ⟨40303092777, 41891180065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 248053760 138362880 139755520 ⟨⟨41600884603, 41600884608⟩, ⟨40806407893, 42398250198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 248053760 248381440 138362880 139755520 ⟨⟨41502540784, 41502540785⟩, ⟨40709027630, 42298937158⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 248381440 248709120 136970240 138362880 ⟨⟨40998404636, 40998404641⟩, ⟨40206761875, 41792923464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248709120 249036800 136970240 138362880 ⟨⟨40901241528, 40901241533⟩, ⟨40110556716, 41694796777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 248381440 248709120 138362880 139755520 ⟨⟨41404326218, 41404326223⟩, ⟨40611774531, 42199755484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248709120 249036800 138362880 139755520 ⟨⟨41306240425, 41306240430⟩, ⟨40514648126, 42100704678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248053760 139755520 141148160 ⟨⟨42008488496, 42008488501⟩, ⟨41213100207, 42806767174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 248053760 248381440 139755520 141148160 ⟨⟨41909221192, 41909221194⟩, ⟨41114797898, 42706529215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 247726080 248053760 141148160 142540800 ⟨⟨42415926844, 42415926849⟩, ⟨41619627202, 43215118373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248053760 248381440 141148160 142540800 ⟨⟨42315737161, 42315737164⟩, ⟨41520403948, 43113956606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 248381440 248709120 139755520 141148160 ⟨⟨41810084091, 41810084096⟩, ⟨41016623699, 42606423574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248709120 249036800 139755520 141148160 ⟨⟨41711076710, 41711076715⟩, ⟨40918577139, 42506449750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 248709120 141148160 142540800 ⟨⟨42215678624, 42215678631⟩, ⟨41421309747, 43012928102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248709120 249036800 141148160 142540800 ⟨⟨42115750747, 42115750753⟩, ⟨41322344121, 42912032356⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 247726080 249036800 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 248053760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 248709120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 248381440) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 248053760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 248709120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (189/640 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
