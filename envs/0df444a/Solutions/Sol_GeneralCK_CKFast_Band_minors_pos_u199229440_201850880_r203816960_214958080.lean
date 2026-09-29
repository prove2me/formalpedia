-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_201850880_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:17:52.140987+00:00
-- url     : https://prove2.me/submissions/e16f93d1-11ec-4e07-b238-c64010657e57

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 77/320]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 199884800 203816960 206602240 ⟨⟨83813658782, 83813658788⟩, ⟨81782813726, 85860401776⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199884800 200540160 203816960 206602240 ⟨⟨83466022380, 83466022386⟩, ⟨81440943280, 85506929938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 199884800 206602240 209387520 ⟨⟨84888830571, 84888830577⟩, ⟨82853648945, 86939908620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 199884800 200540160 206602240 209387520 ⟨⟨84537204506, 84537204512⟩, ⟨82507798341, 86582437890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 200540160 201195520 203816960 206602240 ⟨⟨83119541704, 83119541710⟩, ⟨81100198880, 85154643988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201195520 201850880 203816960 206602240 ⟨⟨82774207857, 82774207859⟩, ⟨80760571872, 84803534781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 200540160 201195520 206602240 209387520 ⟨⟨84186742195, 84186742201⟩, ⟨82163081841, 86226161046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201195520 201850880 206602240 209387520 ⟨⟨83837434705, 83837434709⟩, ⟨81819490754, 85871068903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 199884800 209387520 212172800 ⟨⟨85962567908, 85962567914⟩, ⟨83923058629, 88017971990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 199884800 200540160 209387520 212172800 ⟨⟨85606968060, 85606968066⟩, ⟨83573243602, 87656518397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 199884800 212172800 214958080 ⟨⟨87034879115, 87034879123⟩, ⟨84991051040, 89094600271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 199884800 200540160 212172800 214958080 ⟨⟨86675321246, 86675321252⟩, ⟨84637287202, 88729179723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 200540160 201195520 209387520 212172800 ⟨⟨85252539847, 85252539854⟩, ⟨83224570587, 87296266535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 201195520 201850880 209387520 212172800 ⟨⟨84899274296, 84899274300⟩, ⟨82877030856, 86937207185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 200540160 201195520 212172800 214958080 ⟨⟨86316942740, 86316942748⟩, ⟨84284673141, 88364968601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 201195520 201850880 212172800 214958080 ⟨⟨85959734593, 85959734597⟩, ⟨83933200087, 88001957650⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 201850880 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 199884800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 201195520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 200540160) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 199884800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 201195520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (77/320 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
