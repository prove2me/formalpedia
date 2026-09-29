-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u138936320_141557760_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:27:33.655903+00:00
-- url     : https://prove2.me/submissions/f21aa821-e37f-4ca2-bc15-1367a04f4387

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [53/320, 27/160]`, `ρ ∈ [109/640, 59/320]` by 14 cells of the computing
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
theorem cell0 : cellOK 138936320 139591680 142868480 145817600 ⟨⟨88890348994, 88890348998⟩, ⟨86213199082, 91595176007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 139591680 140247040 142868480 145817600 ⟨⟨88499936914, 88499936921⟩, ⟨85833068123, 91194303471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 138936320 139591680 145817600 148766720 ⟨⟨90555556645, 90555556649⟩, ⟨87872325049, 93266402895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 139591680 140247040 145817600 148766720 ⟨⟨90158954188, 90158954197⟩, ⟨87486013095, 92859331938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 140247040 140902400 142868480 145817600 ⟨⟨88111714784, 88111714791⟩, ⟨85455049222, 90795700610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 140902400 141557760 142868480 145817600 ⟨⟨87725659738, 87725659745⟩, ⟨85079120433, 90399343616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 140247040 140902400 145817600 148766720 ⟨⟨89764564017, 89764564026⟩, ⟨87101835726, 92454552778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 140902400 141557760 145817600 148766720 ⟨⟨89372363132, 89372363141⟩, ⟨86719770850, 92052041482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 138936320 139591680 148766720 151715840 ⟨⟨92215661817, 92215661820⟩, ⟨89526396120, 94932479568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 139591680 140247040 148766720 151715840 ⟨⟨91812924709, 91812924718⟩, ⟨89133958258, 94519266553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 138936320 140247040 151715840 154664960 ⟨⟨93666019750, 93666019757⟩, ⟨89391243397, 98009990185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 140247040 140902400 148766720 151715840 ⟨⟨91412421614, 91412421621⟩, ⟨88743676901, 94108366838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 140902400 141557760 148766720 151715840 ⟨⟨91014129399, 91014129406⟩, ⟨88355529828, 93699756367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 140247040 141557760 151715840 154664960 ⟨⟨92852890672, 92852890674⟩, ⟨88607638183, 97166532213⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 138936320 141557760 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 140247040) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 139591680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 139591680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 140902400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 140902400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 140247040) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 139591680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 151715840) (by decide) (join_su (m := 140902400) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (53/320 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
