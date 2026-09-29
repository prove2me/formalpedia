-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r393216000_415498240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:07:27.65529+00:00
-- url     : https://prove2.me/submissions/6e26623a-7a0a-4264-9b95-4d061dd5037b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [15/32, 317/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 393216000 398786560 ⟨⟨127430792608, 127430792616⟩, ⟨123366721826, 131548544751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231997440 233308160 393216000 398786560 ⟨⟨126371934699, 126371934703⟩, ⟨122328095023, 130469139177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231997440 398786560 404357120 ⟨⟨129116025704, 129116025712⟩, ⟨125037311156, 133248450723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 398786560 404357120 ⟨⟨128044834206, 128044834209⟩, ⟨123986394410, 132156670793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233308160 234618880 393216000 398786560 ⟨⟨125317237256, 125317237264⟩, ⟨121293482414, 129394043000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234618880 235929600 393216000 398786560 ⟨⟨124266647717, 124266647724⟩, ⟨120262833160, 128323201893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 234618880 398786560 404357120 ⟨⟨126977812790, 126977812798⟩, ⟨122939502261, 131069209024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234618880 235929600 398786560 404357120 ⟨⟨125914908961, 125914908969⟩, ⟨121896583912, 129986011177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231997440 404357120 409927680 ⟨⟨130798975293, 130798975299⟩, ⟨126705634531, 134946054569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 233308160 404357120 409927680 ⟨⟨129715501343, 129715501345⟩, ⟨125642478107, 133841952315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231997440 409927680 415498240 ⟨⟨132479665966, 132479665973⟩, ⟨128371716308, 136641381121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231997440 233308160 409927680 415498240 ⟨⟨131383960049, 131383960052⟩, ⟨127296369825, 135525007908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233308160 234618880 404357120 409927680 ⟨⟨128636206248, 128636206254⟩, ⟨124583355851, 132742176124⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234618880 235929600 404357120 409927680 ⟨⟨127561037585, 127561037592⟩, ⟨123528217021, 131646671857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233308160 234618880 409927680 415498240 ⟨⟨130292440927, 130292440934⟩, ⟨126225066266, 134412967818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 409927680 415498240 ⟨⟨129205056263, 129205056270⟩, ⟨125157754953, 133305206815⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 393216000 415498240 t = true :=
  ⟨_, (join_sr (m := 404357120) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 398786560) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231997440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 398786560) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234618880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233308160) (by decide) (join_sr (m := 409927680) (by decide) (join_su (m := 231997440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231997440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 409927680) (by decide) (join_su (m := 234618880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 234618880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (317/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
