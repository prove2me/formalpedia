-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_201850880_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:15:59.7071+00:00
-- url     : https://prove2.me/submissions/d496aff3-83b5-4caa-9a3b-083590dfa94b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 77/320]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 199884800 181534720 184320000 ⟨⟨75159629043, 75159629050⟩, ⟨73163804993, 77171359318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199884800 200540160 181534720 184320000 ⟨⟨74844496541, 74844496548⟩, ⟨72854356933, 76850470702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 199884800 184320000 187105280 ⟨⟨76246582058, 76246582065⟩, ⟨74246347861, 78262721823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 199884800 200540160 184320000 187105280 ⟨⟨75927328362, 75927328369⟩, ⟨73932789338, 77937701550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 200540160 201195520 181534720 184320000 ⟨⟨74530449897, 74530449903⟩, ⟨72545964885, 76530698306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201195520 201850880 181534720 184320000 ⟨⟨74217480570, 74217480574⟩, ⟨72238620559, 76212033331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 200540160 201195520 184320000 187105280 ⟨⟨75609169820, 75609169826⟩, ⟨73620296140, 77613806774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201195520 201850880 184320000 187105280 ⟨⟨75292097843, 75292097847⟩, ⟨73308859927, 77291028649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 199884800 187105280 189890560 ⟨⟨77332032233, 77332032240⟩, ⟨75327397306, 79352571958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 199884800 200540160 187105280 189890560 ⟨⟨77008674229, 77008674236⟩, ⟨75009745052, 79023437073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 199884800 189890560 192675840 ⟨⟨78415988296, 78415988302⟩, ⟨76406961996, 80440918516⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 199884800 200540160 189890560 192675840 ⟨⟨78088542741, 78088542747⟩, ⟨76085232608, 80107685936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 200540160 201195520 187105280 189890560 ⟨⟨76686420511, 76686420519⟩, ⟨74693167270, 78695436798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 201195520 201850880 187105280 189890560 ⟨⟨76365262444, 76365262447⟩, ⟨74377655572, 78368562239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 200540160 201195520 189890560 192675840 ⟨⟨77762210442, 77762210448⟩, ⟨75764586683, 79775596911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 201195520 201850880 189890560 192675840 ⟨⟨77436982717, 77436982719⟩, ⟨75445015781, 79444642505⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 201850880 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 199884800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 201195520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 200540160) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 199884800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 201195520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (77/320 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
