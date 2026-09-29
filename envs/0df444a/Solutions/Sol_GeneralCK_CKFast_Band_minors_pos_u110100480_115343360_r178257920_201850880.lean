-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_115343360_r178257920_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:31:24.719655+00:00
-- url     : https://prove2.me/submissions/33272947-b77f-4e6b-af69-720ca43d8932

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 11/80]`, `ρ ∈ [17/80, 77/320]` by 19 cells of the computing
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
theorem cell0 : cellOK 110100480 111411200 178257920 184156160 ⟨⟨132300295615, 132300295626⟩, ⟨125760183093, 138983756794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 111411200 112721920 178257920 181207040 ⟨⟨130179741453, 130179741463⟩, ⟨125064942064, 135382601798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 111411200 112721920 181207040 184156160 ⟨⟨132032271580, 132032271589⟩, ⟨126907608795, 137244695955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110100480 111411200 184156160 190054400 ⟨⟨136016119372, 136016119382⟩, ⟨129454877588, 142719519293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 111411200 112721920 184156160 190054400 ⟨⟨134797871699, 134797871707⟩, ⟨128294380122, 141441528452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112721920 114032640 178257920 181207040 ⟨⟨129007959038, 129007959048⟩, ⟨123935010240, 134167805175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 112721920 114032640 181207040 184156160 ⟨⟨130847986814, 130847986822⟩, ⟨125765136946, 136017446691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 114032640 115343360 178257920 181207040 ⟨⟨127851140233, 127851140237⟩, ⟨122819308230, 132968731648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 114032640 115343360 181207040 184156160 ⟨⟨129678734129, 129678734132⟩, ⟨124636967331, 134805984599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 112721920 114032640 184156160 190054400 ⟨⟨133595105607, 133595105617⟩, ⟨127148376874, 140180050194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 114032640 115343360 184156160 190054400 ⟨⟨132407468633, 132407468637⟩, ⟨126016540978, 138934705161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 110100480 111411200 190054400 195952640 ⟨⟨139703622471, 139703622481⟩, ⟨133121777822, 146426440275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 111411200 112721920 190054400 195952640 ⟨⟨138461110250, 138461110261⟩, ⟨131936867425, 145124376775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 110100480 111411200 195952640 201850880 ⟨⟨143363424241, 143363424252⟩, ⟨136761484783, 150105157538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 111411200 112721920 195952640 201850880 ⟨⟨142097208893, 142097208901⟩, ⟨135552712306, 148779592749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112721920 114032640 190054400 195952640 ⟨⟨137234198232, 137234198243⟩, ⟨130766581569, 143838931207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 114032640 115343360 190054400 195952640 ⟨⟨136022534528, 136022534532⟩, ⟨129610593415, 142569725403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 112721920 114032640 195952640 201850880 ⟨⟨140846701014, 140846701024⟩, ⟨134358683461, 147470739808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 114032640 115343360 195952640 201850880 ⟨⟨139611549537, 139611549541⟩, ⟨133179071694, 146178221965⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 115343360 178257920 201850880 t = true :=
  ⟨_, (join_sr (m := 190054400) (by decide) (join_su (m := 112721920) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 111411200) (by decide) (leaf_ok cell0) (join_sr (m := 181207040) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 111411200) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 184156160) (by decide) (join_su (m := 114032640) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 181207040) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 114032640) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_su (m := 112721920) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 111411200) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 111411200) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 195952640) (by decide) (join_su (m := 114032640) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 114032640) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
