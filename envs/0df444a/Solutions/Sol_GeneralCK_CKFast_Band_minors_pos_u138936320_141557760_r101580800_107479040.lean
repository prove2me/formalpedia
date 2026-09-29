-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u138936320_141557760_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:09:19.797017+00:00
-- url     : https://prove2.me/submissions/3746d8a8-f387-4acc-92f6-7e9ab08cc881

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [53/320, 27/160]`, `ρ ∈ [31/256, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 138936320 139591680 101580800 103055360 ⟨⟨64577609179, 64577609182⟩, ⟨62525245033, 66647786710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 138936320 139591680 103055360 104529920 ⟨⟨65450025194, 65450025197⟩, ⟨63394667652, 67523183597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 139591680 140247040 101580800 103055360 ⟨⟨64281931531, 64281931540⟩, ⟨62236849982, 66344712137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 139591680 140247040 103055360 104529920 ⟨⟨65150802913, 65150802921⟩, ⟨63102736411, 67216556315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 138936320 139591680 104529920 106004480 ⟨⟨66320975066, 66320975067⟩, ⟨64262635058, 68397103349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 138936320 139591680 106004480 107479040 ⟨⟨67190465828, 67190465831⟩, ⟨65129154219, 69269553072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 139591680 140247040 104529920 106004480 ⟨⟨66018225189, 66018225195⟩, ⟨63967184502, 68086940556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 139591680 140247040 106004480 107479040 ⟨⟨66884205272, 66884205279⟩, ⟨64830201101, 68955871849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 140247040 140902400 101580800 103055360 ⟨⟨63988051091, 63988051099⟩, ⟨61950192864, 66043495297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 140247040 140902400 103055360 104529920 ⟨⟨64853394224, 64853394231⟩, ⟨62812559497, 66911803131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 140902400 141557760 101580800 103055360 ⟨⟨63695947891, 63695947899⟩, ⟨61665254443, 65744115473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 140902400 141557760 103055360 104529920 ⟨⟨64557779023, 64557779030⟩, ⟨62524117540, 66608903195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 140247040 140902400 104529920 106004480 ⟨⟨65717305079, 65717305086⟩, ⟨63673504461, 67778668019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 140247040 140902400 106004480 107479040 ⟨⟨66579790455, 66579790463⟩, ⟨64533034485, 68644096832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 140902400 141557760 104529920 106004480 ⟨⟨65418194501, 65418194507⟩, ⟨63381575430, 67472264754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140902400 141557760 106004480 107479040 ⟨⟨66277201011, 66277201019⟩, ⟨64237634735, 68334206907⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 138936320 141557760 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 140247040) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 139591680) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 103055360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 139591680) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 106004480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 104529920) (by decide) (join_su (m := 140902400) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 103055360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 140902400) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 106004480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (53/320 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
