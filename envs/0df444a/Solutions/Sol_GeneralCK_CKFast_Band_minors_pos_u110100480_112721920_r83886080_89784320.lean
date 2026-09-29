-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_112721920_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:04:44.736742+00:00
-- url     : https://prove2.me/submissions/fed842b3-5527-4dc4-9802-d9b0bdba003c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 43/320]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 110100480 110755840 83886080 85360640 ⟨⟨66971789276, 66971789286⟩, ⟨64568119520, 69400370914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 110100480 110755840 85360640 86835200 ⟨⟨68049673108, 68049673116⟩, ⟨65642409703, 70481810284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110755840 111411200 83886080 85360640 ⟨⟨66627066652, 66627066662⟩, ⟨64234159068, 69044679765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110755840 111411200 85360640 86835200 ⟨⟨67700144129, 67700144136⟩, ⟨65303652718, 70121303877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 110100480 110755840 86835200 88309760 ⟨⟨69124888353, 69124888360⟩, ⟨66714054936, 71560557369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 110100480 110755840 88309760 89784320 ⟨⟨70197451849, 70197451857⟩, ⟨67783071834, 72636629234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110755840 111411200 86835200 88309760 ⟨⟨68770586565, 68770586575⟩, ⟨66370534600, 71195269622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 110755840 111411200 88309760 89784320 ⟨⟨69838410490, 69838410498⟩, ⟨67434821013, 72266593745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 111411200 112066560 83886080 85360640 ⟨⟨66285104469, 66285104477⟩, ⟨63902849053, 68691861907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 111411200 112066560 85360640 86835200 ⟨⟨67353404822, 67353404830⟩, ⟨64967575485, 69763699894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 112066560 112721920 83886080 85360640 ⟨⟨65945864631, 65945864640⟩, ⟨63574153090, 68341877485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 112066560 112721920 85360640 86835200 ⟨⟨67009416800, 67009416808⟩, ⟨64634141314, 69408958195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 111411200 112066560 86835200 88309760 ⟨⟨68419103210, 68419103218⟩, ⟨66029722854, 70832912953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 111411200 112066560 88309760 89784320 ⟨⟨69482215849, 69482215856⟩, ⟨67089307160, 71899517511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 112066560 112721920 86835200 88309760 ⟨⟨68070399607, 68070399616⟩, ⟨65691582720, 70473446934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 112066560 112721920 88309760 89784320 ⟨⟨69128828968, 69128828975⟩, ⟨66746493011, 71535359831⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 112721920 83886080 89784320 t = true :=
  ⟨_, (join_su (m := 111411200) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 110755840) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 85360640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 110755840) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 88309760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 86835200) (by decide) (join_su (m := 112066560) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 85360640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 112066560) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 88309760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (43/320 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
