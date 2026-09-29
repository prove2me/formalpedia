-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r348651520_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:47:13.803009+00:00
-- url     : https://prove2.me/submissions/d6635d1f-8cdf-4c93-a0a7-2daa24336f2b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [133/320, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 348651520 354222080 ⟨⟨156227200678, 156227200685⟩, ⟨151336012385, 161188533552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 179568640 180879360 348651520 354222080 ⟨⟨155053374873, 155053374876⟩, ⟨150190116403, 159986268968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 179568640 354222080 359792640 ⟨⟨158455782142, 158455782151⟩, ⟨153548603341, 163432956309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 354222080 359792640 ⟨⟨157268560522, 157268560526⟩, ⟨152389311911, 162217302716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 180879360 182190080 348651520 354222080 ⟨⟨153886501545, 153886501552⟩, ⟨149050910526, 158791224742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182190080 183500800 348651520 354222080 ⟨⟨152726483051, 152726483058⟩, ⟨147918300965, 157603299284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 182190080 354222080 359792640 ⟨⟨156088303686, 156088303694⟩, ⟨151236725009, 161008879500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182190080 183500800 354222080 359792640 ⟨⟨154914914312, 154914914321⟩, ⟨150090749112, 159807585463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 179568640 359792640 365363200 ⟨⟨160678652382, 160678652389⟩, ⟨155755558026, 165671591313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 179568640 180879360 359792640 365363200 ⟨⟨159478142409, 159478142413⟩, ⟨154582976806, 164442657971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 179568640 365363200 370933760 ⟨⟨162895885274, 162895885283⟩, ⟨157956949133, 167904513637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 179568640 180879360 365363200 370933760 ⟨⟨161682192600, 161682192604⟩, ⟨156771182013, 166662407960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 359792640 365363200 ⟨⟨158284607934, 158284607942⟩, ⟨153417112968, 163220963418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182190080 183500800 359792640 365363200 ⟨⟨157097951980, 157097951988⟩, ⟨152257873271, 162006406858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 180879360 182190080 365363200 370933760 ⟨⟨160475484589, 160475484598⟩, ⟨155592143598, 165427547910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182190080 183500800 365363200 370933760 ⟨⟨159275664622, 159275664631⟩, ⟨154419740943, 164199833120⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 348651520 370933760 t = true :=
  ⟨_, (join_sr (m := 359792640) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 179568640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 179568640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 354222080) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182190080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 180879360) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 179568640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 179568640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 365363200) (by decide) (join_su (m := 182190080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 182190080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
