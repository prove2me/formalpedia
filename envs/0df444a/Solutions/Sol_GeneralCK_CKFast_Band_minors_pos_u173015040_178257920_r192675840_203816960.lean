-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:38:13.138676+00:00
-- url     : https://prove2.me/submissions/e886e12c-7125-45b5-9540-48cf1bc8ee81

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 192675840 195461120 ⟨⟨93598374078, 93598374083⟩, ⟨89884523455, 97363138526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173015040 174325760 195461120 198246400 ⟨⟨94846936910, 94846936915⟩, ⟨91124473171, 98620298008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 174325760 175636480 192675840 195461120 ⟨⟨92832170246, 92832170254⟩, ⟨89138897763, 96575908525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 195461120 198246400 ⟨⟨94071878443, 94071878450⟩, ⟨90370022304, 97824186193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 174325760 198246400 201031680 ⟨⟨96093240531, 96093240536⟩, ⟨92362189116, 99875172374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 173015040 174325760 201031680 203816960 ⟨⟨97337300153, 97337300158⟩, ⟨93597686291, 101127777042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 174325760 175636480 198246400 201031680 ⟨⟨95309375115, 95309375123⟩, ⟨91598960022, 99070227171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 174325760 175636480 201031680 203816960 ⟨⟨96544675035, 96544675042⟩, ⟨92825725488, 100314046433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 175636480 176947200 192675840 195461120 ⟨⟨92072100860, 92072100868⟩, ⟨88399155597, 95795070926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 175636480 176947200 195461120 198246400 ⟨⟨93302996129, 93302996137⟩, ⟨89621497062, 97034508027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 176947200 178257920 192675840 195461120 ⟨⟨91318063313, 91318063320⟩, ⟨87665198949, 95020518379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 176947200 178257920 195461120 198246400 ⟨⟨92540186983, 92540186989⟩, ⟨88878799036, 96251155803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 175636480 176947200 198246400 201031680 ⟨⟨94531726649, 94531726657⟩, ⟨90841697758, 98271755941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 176947200 201031680 203816960 ⟨⟨95758306769, 95758306776⟩, ⟨92059771842, 99506829206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 176947200 178257920 198246400 201031680 ⟨⟨93760191786, 93760191794⟩, ⟨90090303531, 97479650635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 176947200 178257920 201031680 203816960 ⟨⟨94978091660, 94978091668⟩, ⟨91299726188, 98706016993⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 192675840 203816960 t = true :=
  ⟨_, (join_su (m := 175636480) (by decide) (join_sr (m := 198246400) (by decide) (join_su (m := 174325760) (by decide) (join_sr (m := 195461120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 195461120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 174325760) (by decide) (join_sr (m := 201031680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 201031680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 198246400) (by decide) (join_su (m := 176947200) (by decide) (join_sr (m := 195461120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 195461120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 176947200) (by decide) (join_sr (m := 201031680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 201031680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
