-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r343408640_367001600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:03:30.464674+00:00
-- url     : https://prove2.me/submissions/1a85d7a4-50c1-400b-b20d-66705f9f7e17

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [131/320, 7/16]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 343408640 349306880 ⟨⟨183754820885, 183754820895⟩, ⟨174463611744, 193277610094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 149422080 349306880 355205120 ⟨⟨186458679008, 186458679018⟩, ⟨177136533397, 196011515792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 149422080 152043520 343408640 349306880 ⟨⟨181049273881, 181049273886⟩, ⟨171863675569, 190463156067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 349306880 355205120 ⟨⟨183724167662, 183724167665⟩, ⟨174507440611, 193168356592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 149422080 355205120 361103360 ⟨⟨189152610794, 189152610802⟩, ⟨179799753119, 198735265359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 149422080 361103360 367001600 ⟨⟨191836773300, 191836773311⟩, ⟨182453423423, 201449020480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 152043520 355205120 361103360 ⟨⟨186389475820, 186389475824⟩, ⟨177141836060, 195863749785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 149422080 152043520 361103360 367001600 ⟨⟨189045348072, 189045348077⟩, ⟨179767007347, 198549489718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 154664960 343408640 349306880 ⟨⟨178382509978, 178382509988⟩, ⟨169300198580, 187689887775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 152043520 154664960 349306880 355205120 ⟨⟨181028444548, 181028444557⟩, ⟨171914837828, 190366359436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 157286400 343408640 349306880 ⟨⟨175753344548, 175753344556⟩, ⟨166772073407, 184956540937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 154664960 157286400 349306880 355205120 ⟨⟨178370332129, 178370332139⟩, ⟨169357623298, 187604268763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152043520 154664960 355205120 361103360 ⟨⟨183665124889, 183665124897⟩, ⟨174520430576, 193033363211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 152043520 154664960 361103360 367001600 ⟨⟨186292693690, 186292693700⟩, ⟨177117115483, 195691045889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 154664960 157286400 355205120 361103360 ⟨⟨180978387732, 180978387739⟩, ⟨171934440733, 190242858952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 154664960 157286400 361103360 367001600 ⟨⟨183577647328, 183577647338⟩, ⟨174502657902, 192872451336⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 343408640 367001600 t = true :=
  ⟨_, (join_su (m := 152043520) (by decide) (join_sr (m := 355205120) (by decide) (join_su (m := 149422080) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 349306880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 149422080) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 361103360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 355205120) (by decide) (join_su (m := 154664960) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 349306880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 154664960) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 361103360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (131/320 : ℝ) (7/16 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  have e3 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
