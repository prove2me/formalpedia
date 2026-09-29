-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_212336640_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:36:14.498872+00:00
-- url     : https://prove2.me/submissions/a74da175-bc82-47b9-9572-64493ca6ae47

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 81/320]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 210370560 192675840 195461120 ⟨⟨74324100190, 74324100196⟩, ⟨72398875098, 76264156275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 210370560 211025920 192675840 195461120 ⟨⟨74009533581, 74009533588⟩, ⟨72089586681, 75944248342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 210370560 195461120 198246400 ⟨⟨75341236858, 75341236865⟩, ⟨73411802796, 77285504754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 210370560 211025920 195461120 198246400 ⟨⟨75022749025, 75022749031⟩, ⟨73098603515, 76961665451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 211025920 211681280 192675840 195461120 ⟨⟨73695958716, 73695958720⟩, ⟨71781263877, 75625358712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 211681280 212336640 192675840 195461120 ⟨⟨73383368066, 73383368073⟩, ⟨71473899367, 75307479647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 211025920 211681280 195461120 198246400 ⟨⟨74705260899, 74705260902⟩, ⟨72786377819, 76638852400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 211681280 212336640 195461120 198246400 ⟨⟨74388764908, 74388764915⟩, ⟨72475118349, 76317057826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 210370560 198246400 201031680 ⟨⟨76357149189, 76357149195⟩, ⟨74423513074, 78305621884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 210370560 211025920 198246400 201031680 ⟨⟨76034754153, 76034754160⟩, ⟨74106416825, 77977865363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209715200 210370560 201031680 203816960 ⟨⟨77371843900, 77371843907⟩, ⟨75434012607, 79324514428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 210370560 211025920 201031680 203816960 ⟨⟨77045555585, 77045555592⟩, ⟨75113033187, 78992854737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 211025920 211681280 198246400 201031680 ⟨⟨75713366652, 75713366655⟩, ⟨73790302000, 77651142905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 211681280 212336640 198246400 201031680 ⟨⟨75392979075, 75392979081⟩, ⟨73475161198, 77325446697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 211025920 211681280 201031680 203816960 ⟨⟨76720282499, 76720282502⟩, ⟨74793042896, 78662236788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 211681280 212336640 201031680 203816960 ⟨⟨76396016989, 76396016995⟩, ⟨74474034294, 78332652726⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 212336640 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 211025920) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 210370560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 210370560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 211681280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 211025920) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 210370560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 210370560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 211681280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 211681280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (81/320 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
