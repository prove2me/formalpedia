-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r367001600_390594560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:46:59.401051+00:00
-- url     : https://prove2.me/submissions/5c7b2e20-6600-489b-a288-33f36c36f820

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [7/16, 149/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 367001600 372899840 ⟨⟨206201162642, 206201162647⟩, ⟨196344611324, 216298529470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 138936320 372899840 378798080 ⟨⟨208976347514, 208976347519⟩, ⟨199090917946, 219101387247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 138936320 141557760 367001600 372899840 ⟨⟨203214251270, 203214251279⟩, ⟨193472157959, 213193845281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 372899840 378798080 ⟨⟨205962002494, 205962002504⟩, ⟨196190687101, 215969692299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 138936320 378798080 384696320 ⟨⟨211740886354, 211740886357⟩, ⟨201826814736, 221893359483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 138936320 384696320 390594560 ⟨⟨214494956143, 214494956148⟩, ⟨204552473462, 224674628434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 138936320 141557760 378798080 384696320 ⟨⟨208699453635, 208699453645⟩, ⟨198899145062, 218735006476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 138936320 141557760 384696320 390594560 ⟨⟨211426773736, 211426773745⟩, ⟨201597695952, 221489961852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 144179200 367001600 372899840 ⟨⟨200271203553, 200271203563⟩, ⟨190641027250, 210135639743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 141557760 144179200 372899840 378798080 ⟨⟨202991453409, 202991453419⟩, ⟨193331743672, 212884372204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 144179200 146800640 367001600 372899840 ⟨⟨197370661226, 197370661236⟩, ⟨187849946546, 207122467023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 144179200 146800640 372899840 378798080 ⟨⟨200063352425, 200063352435⟩, ⟨190512823656, 209843993525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 141557760 144179200 378798080 384696320 ⟨⟨205701740555, 205701740563⟩, ⟨196012718942, 215622916068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 141557760 144179200 384696320 390594560 ⟨⟨208402226421, 208402226431⟩, ⟨198684109820, 218351437501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 144179200 146800640 378798080 384696320 ⟨⟨202746409820, 202746409828⟩, ⟨193166281142, 212555667302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 144179200 146800640 384696320 390594560 ⟨⟨205419987552, 205419987562⟩, ⟨195810468737, 215257646972⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 367001600 390594560 t = true :=
  ⟨_, (join_su (m := 141557760) (by decide) (join_sr (m := 378798080) (by decide) (join_su (m := 138936320) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 372899840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 138936320) (by decide) (join_sr (m := 384696320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 384696320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 378798080) (by decide) (join_su (m := 144179200) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 372899840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 144179200) (by decide) (join_sr (m := 384696320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 384696320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (7/16 : ℝ) (149/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  have e3 : (((390594560 : ℤ) : ℝ) / (D : ℝ)) = (149/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
