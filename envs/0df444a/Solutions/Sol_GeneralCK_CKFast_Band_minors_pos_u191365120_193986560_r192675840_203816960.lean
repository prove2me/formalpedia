-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u191365120_193986560_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:49.11838+00:00
-- url     : https://prove2.me/submissions/9b192ffe-77fc-49aa-9d30-a935c9d55950

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [73/320, 37/160]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 191365120 192020480 192675840 195461120 ⟨⟨83567472926, 83567472929⟩, ⟨81482931236, 85668805387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 192020480 192675840 192675840 195461120 ⟨⟨83221779170, 83221779176⟩, ⟨81143341496, 85316930638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 192020480 195461120 198246400 ⟨⟨84697810617, 84697810620⟩, ⟨82608776791, 86803630488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 192020480 192675840 195461120 198246400 ⟨⟨84347955171, 84347955178⟩, ⟨82265035136, 86447584603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 192675840 193331200 192675840 195461120 ⟨⟨82877319085, 82877319092⟩, ⟨80804952463, 84966323082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193331200 193986560 192675840 195461120 ⟨⟨82534082861, 82534082867⟩, ⟨80467754613, 84616972620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 192675840 193331200 195461120 198246400 ⟨⟨83999342583, 83999342591⟩, ⟨81922503410, 86092815057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 193331200 193986560 195461120 198246400 ⟨⟨83651962997, 83651963005⟩, ⟨81581172040, 85739311711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 191365120 192020480 198246400 201031680 ⟨⟨85826470724, 85826470727⟩, ⟨83732955900, 87936766751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 192020480 192675840 198246400 201031680 ⟨⟨85472471974, 85472471980⟩, ⟨83385080540, 87576568289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 191365120 192020480 201031680 203816960 ⟨⟨86953463418, 86953463421⟩, ⟨84855478650, 89068224429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 192020480 192675840 201031680 203816960 ⟨⟨86595339599, 86595339606⟩, ⟨84503487652, 88703891800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 192675840 193331200 198246400 201031680 ⟨⟨85119725091, 85119725098⟩, ⟨83038424158, 87217655138⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193331200 193986560 198246400 201031680 ⟨⟨84768220178, 84768220184⟩, ⟨82692977131, 86860017114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 192675840 193331200 201031680 203816960 ⟨⟨86238476486, 86238476492⟩, ⟨84152724503, 88340853277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 193331200 193986560 201031680 203816960 ⟨⟨85882864136, 85882864143⟩, ⟨83803179540, 87979098636⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 191365120 193986560 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 192675840) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 192020480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 192020480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 193331200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 193331200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 192675840) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 192020480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 192020480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 193331200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 193331200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (73/320 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
