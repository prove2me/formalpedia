-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_128450560_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:52:52.521232+00:00
-- url     : https://prove2.me/submissions/733b649c-5140-4720-b4cb-1bc091c0fd6e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 49/320]`, `ρ ∈ [31/256, 41/320]` by 14 cells of the computing
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
theorem cell0 : cellOK 125829120 126484480 101580800 103055360 ⟨⟨70902188837, 70902188842⟩, ⟨68690478778, 73134294656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 125829120 126484480 103055360 104529920 ⟨⟨71849161630, 71849161634⟩, ⟨69634293879, 74084403558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 126484480 127139840 101580800 103055360 ⟨⟨70565865886, 70565865895⟩, ⟨68362798788, 72789184773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 126484480 127139840 103055360 104529920 ⟨⟨71508935404, 71508935413⟩, ⟨69302718502, 73735383058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 125829120 126484480 104529920 107479040 ⟨⟨73266145279, 73266145285⟩, ⟨70452435593, 76112775227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 126484480 127139840 104529920 107479040 ⟨⟨72920105099, 72920105106⟩, ⟨70118314119, 75754568419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 127139840 127795200 101580800 103055360 ⟨⟨70231811092, 70231811099⟩, ⟨68037310049, 72446421663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 127139840 127795200 103055360 104529920 ⟨⟨71170996761, 71170996769⟩, ⟨68973353850, 73388728697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 127795200 128450560 101580800 103055360 ⟨⟨69899997204, 69899997211⟩, ⟨67713986350, 72105977016⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 127795200 128450560 103055360 104529920 ⟨⟨70835318286, 70835318293⟩, ⟨68646173545, 73044412004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 127139840 127795200 104529920 106004480 ⟨⟨72108370622, 72108370629⟩, ⟨69907600162, 74329209540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 127139840 127795200 106004480 107479040 ⟨⟨73043942253, 73043942262⟩, ⟨70840058459, 75267873882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 127795200 128450560 104529920 106004480 ⟨⟨71768848879, 71768848886⟩, ⟨69576584360, 73981042334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 127795200 128450560 106004480 107479040 ⟨⟨72700598400, 72700598409⟩, ⟨70505228103, 74915877530⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 128450560 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 127139840) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 126484480) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 103055360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 126484480) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 104529920) (by decide) (join_su (m := 127795200) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 103055360) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 127795200) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 106004480) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (49/320 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((128450560 : ℤ) : ℝ) / (D : ℝ)) = (49/320 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
