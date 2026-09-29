-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u207093760_209715200_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:51:09.437985+00:00
-- url     : https://prove2.me/submissions/7753751e-53e6-4b44-9804-116fd4bdd9e8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [79/320, 1/4]`, `ρ ∈ [3/20, 401/2560]` by 18 cells of the computing
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
theorem cell0 : cellOK 207093760 207749120 125829120 127221760 ⟨⟨50132272695, 50132272702⟩, ⟨48596324308, 51678369629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 207093760 207749120 127221760 128614400 ⟨⟨50665596997, 50665597004⟩, ⟨49127632294, 52213714327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 207749120 208404480 125829120 127221760 ⟨⟨49914296917, 49914296920⟩, ⟨48381970522, 51456730557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 207749120 208404480 127221760 128614400 ⟨⟨50445448173, 50445448176⟩, ⟨48911111176, 51989896549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 207093760 207749120 128614400 130007040 ⟨⟨51198553349, 51198553356⟩, ⟨49658573899, 52748689485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 207093760 207749120 130007040 131399680 ⟨⟨51731142778, 51731142785⟩, ⟨50189150146, 53283296136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207749120 208404480 128614400 130007040 ⟨⟨50976235847, 50976235850⟩, ⟨49439889786, 52522697404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 207749120 208404480 130007040 131399680 ⟨⟨51506660955, 51506660958⟩, ⟨49968307361, 53055134138⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 208404480 208732160 125829120 127221760 ⟨⟨49751325926, 49751325932⟩, ⟨48833354993, 50673018942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 208732160 209059840 125829120 127221760 ⟨⟨49642920376, 49642920379⟩, ⟨48726216455, 50563337709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 208404480 209059840 127221760 128614400 ⟨⟨50226083297, 50226083302⟩, ⟨48695353776, 51766883267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 209059840 209387520 125829120 127221760 ⟨⟨49534707324, 49534707331⟩, ⟨48619267089, 50453852337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 209387520 209715200 125829120 127221760 ⟨⟨49426685993, 49426685998⟩, ⟨48512506136, 50344562024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 209059840 209715200 127221760 128614400 ⟨⟨50007496011, 50007496016⟩, ⟨48480353905, 51544667942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209059840 128614400 130007040 ⟨⟨50754708298, 50754708303⟩, ⟨49221975383, 52297515833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 208404480 209059840 130007040 131399680 ⟨⟨51282975039, 51282975044⟩, ⟨49748240230, 52827788619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 209059840 209715200 128614400 130007040 ⟨⟨50533964301, 50533964306⟩, ⟨49004824457, 52073138195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 209059840 209715200 130007040 131399680 ⟨⟨51060078593, 51060078600⟩, ⟨49528942482, 52601252961⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 207093760 209715200 125829120 131399680 t = true :=
  ⟨_, (join_su (m := 208404480) (by decide) (join_sr (m := 128614400) (by decide) (join_su (m := 207749120) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 127221760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 207749120) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 130007040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 128614400) (by decide) (join_su (m := 209059840) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 208732160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 127221760) (by decide) (join_su (m := 209387520) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))) (join_su (m := 209059840) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 130007040) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (79/320 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
