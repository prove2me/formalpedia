-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r326369280_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:04:29.157312+00:00
-- url     : https://prove2.me/submissions/ca64139c-d292-446c-9483-5cdcab4e8405

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [249/640, 133/320]` by 17 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 326369280 331939840 ⟨⟨118230176995, 118230177003⟩, ⟨114094863632, 122423223312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 216268800 217579520 326369280 331939840 ⟨⟨117271501707, 117271501715⟩, ⟨113157842380, 121442498885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 216268800 331939840 337510400 ⟨⟨120102469611, 120102469619⟩, ⟨115951674526, 124311001826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 331939840 337510400 ⟨⟨119130536491, 119130536499⟩, ⟨115001441945, 123316976651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 217579520 218890240 326369280 331939840 ⟨⟨116317491584, 116317491591⟩, ⟨112225305442, 120466624568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 218890240 220200960 326369280 329154560 ⟨⟨114909437547, 114909437550⟩, ⟨111441564324, 118417262248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218890240 220200960 329154560 331939840 ⟨⟨115826530068, 115826530070⟩, ⟨112351511613, 119341521614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 217579520 218890240 331939840 337510400 ⟨⟨118163290175, 118163290183⟩, ⟨114055716160, 122327822292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 218890240 220200960 331939840 337510400 ⟨⟨117200668223, 117200668227⟩, ⟨113114437128, 121343473853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 216268800 337510400 343080960 ⟨⟨121971367879, 121971367886⟩, ⟨117805125395, 126195350375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 216268800 217579520 337510400 343080960 ⟨⟨120986250183, 120986250191⟩, ⟨116841753470, 125188099001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 214958080 216268800 343080960 348651520 ⟨⟨123836909135, 123836909141⟩, ⟨119655253135, 128076306738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 216268800 217579520 343080960 348651520 ⟨⟨122838679121, 122838679127⟩, ⟨118678812872, 127055902692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 217579520 218890240 337510400 343080960 ⟨⟨120005839704, 120005839711⟩, ⟨115882909620, 124185737899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 220200960 337510400 343080960 ⟨⟨119030073991, 119030073994⟩, ⟨114928533764, 123188202192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217579520 218890240 343080960 348651520 ⟨⟨121845175532, 121845175539⟩, ⟨117706920780, 126040407153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 218890240 220200960 343080960 348651520 ⟨⟨120856335926, 120856335929⟩, ⟨116739516758, 125029755275⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 326369280 348651520 t = true :=
  ⟨_, (join_sr (m := 337510400) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 216268800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 331939840) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell4) (join_sr (m := 329154560) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 218890240) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 217579520) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 216268800) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 343080960) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 218890240) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
