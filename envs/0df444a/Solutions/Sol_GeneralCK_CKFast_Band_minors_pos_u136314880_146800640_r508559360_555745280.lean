-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r508559360_555745280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:52:59.525969+00:00
-- url     : https://prove2.me/submissions/39fd7524-d57b-48f4-b090-da3a54a3da75

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [97/160, 53/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 508559360 520355840 ⟨⟨271478460236, 271478460240⟩, ⟨258685110612, 284584604798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 138936320 141557760 508559360 520355840 ⟨⟨267903892609, 267903892618⟩, ⟨255252951230, 280864840242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 138936320 520355840 532152320 ⟨⟨276590412835, 276590412840⟩, ⟨263747701605, 289741561743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 520355840 532152320 ⟨⟨272974280883, 272974280894⟩, ⟨260272776776, 285981646177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 144179200 508559360 520355840 ⟨⟨264369655071, 264369655081⟩, ⟨251858777479, 277187757766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 144179200 146800640 508559360 520355840 ⟨⟨260874656174, 260874656185⟩, ⟨248501560159, 273552205254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 141557760 144179200 520355840 532152320 ⟨⟨269398068091, 269398068102⟩, ⟨256835502733, 282263918491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 144179200 146800640 520355840 532152320 ⟨⟨265860704291, 265860704301⟩, ⟨253434868407, 278587251226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 138936320 532152320 543948800 ⟨⟨281674651627, 281674651633⟩, ⟨268783226264, 294870159303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 138936320 141557760 532152320 543948800 ⟨⟨278017725787, 278017725797⟩, ⟨265266296325, 291070869797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 138936320 543948800 555745280 ⟨⟨286732115590, 286732115596⟩, ⟨273792593253, 299971366254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 138936320 141557760 543948800 555745280 ⟨⟨283035131564, 283035131575⟩, ⟨270234384951, 296133444095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 141557760 144179200 532152320 543948800 ⟨⟨274400296279, 274400296289⟩, ⟨261786669370, 287313263445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 144179200 146800640 532152320 543948800 ⟨⟨270821313972, 270821313982⟩, ⟨258343352328, 283596237069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 141557760 144179200 543948800 555745280 ⟨⟨279377210187, 279377210198⟩, ⟨266713119897, 292336690879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 144179200 146800640 543948800 555745280 ⟨⟨275757323101, 275757323112⟩, ⟨263227822873, 288580027313⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 508559360 555745280 t = true :=
  ⟨_, (join_sr (m := 532152320) (by decide) (join_su (m := 141557760) (by decide) (join_sr (m := 520355840) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 138936320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 520355840) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 144179200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 141557760) (by decide) (join_sr (m := 543948800) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 138936320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 543948800) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 144179200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (97/160 : ℝ) (53/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  have e3 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
