-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_146800640_r201850880_213647360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:35:22.702016+00:00
-- url     : https://prove2.me/submissions/b663d5c3-ecf8-48c8-9d16-ad6f490c2dbc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 7/40]`, `ρ ∈ [77/320, 163/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142868480 201850880 204800000 ⟨⟨119025985661, 119025985670⟩, ⟨114638670202, 123479080699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 141557760 142868480 204800000 207749120 ⟨⟨120574168545, 120574168554⟩, ⟨116177303386, 125036700877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 142868480 144179200 201850880 204800000 ⟨⟨118041990436, 118041990445⟩, ⟨113683646051, 122465431879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142868480 144179200 204800000 207749120 ⟨⟨119579886793, 119579886800⟩, ⟨115211999578, 124012763956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 142868480 207749120 210698240 ⟨⟨122118284441, 122118284448⟩, ⟨117711922827, 126590200289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 141557760 142868480 210698240 213647360 ⟨⟨123658368537, 123658368544⟩, ⟨119242563090, 128139614755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 142868480 144179200 207749120 210698240 ⟨⟨121113798040, 121113798049⟩, ⟨116736419956, 125556058422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 142868480 144179200 210698240 213647360 ⟨⟨122643758366, 122643758373⟩, ⟨118256940776, 127095350068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 144179200 145489920 201850880 204800000 ⟨⟨117067606851, 117067606858⟩, ⟨112737824372, 121461816026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 144179200 145489920 204800000 207749120 ⟨⟨118595264744, 118595264752⟩, ⟨114255947781, 122998906423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 145489920 146800640 201850880 204800000 ⟨⟨116102654254, 116102654261⟩, ⟨111801033173, 120468043541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 145489920 146800640 204800000 207749120 ⟨⟨117620121539, 117620121546⟩, ⟨113308975734, 121994938537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 144179200 145489920 207749120 210698240 ⟨⟨120119017851, 120119017860⟩, ⟨115770217108, 124532040783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 144179200 145489920 210698240 213647360 ⟨⟨121638899384, 121638899391⟩, ⟨117280664988, 126061252899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 145489920 146800640 207749120 210698240 ⟨⟨119133762837, 119133762844⟩, ⟨114813141774, 123517957524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 145489920 146800640 210698240 213647360 ⟨⟨120643610408, 120643610416⟩, ⟨116313563001, 125037133327⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 146800640 201850880 213647360 t = true :=
  ⟨_, (join_su (m := 144179200) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 142868480) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 204800000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 142868480) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 210698240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 207749120) (by decide) (join_su (m := 145489920) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 204800000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 145489920) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 210698240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (163/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
