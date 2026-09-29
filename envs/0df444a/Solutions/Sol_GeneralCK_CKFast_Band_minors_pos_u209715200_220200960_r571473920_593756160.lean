-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r571473920_593756160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:53:28.033313+00:00
-- url     : https://prove2.me/submissions/302259a0-9dbb-4cf6-9679-20e3bfc3cd2e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [109/160, 453/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 571473920 577044480 ⟨⟨203088413968, 203088413976⟩, ⟨194748476052, 211594893111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 212336640 577044480 582615040 ⟨⟨204880744519, 204880744528⟩, ⟨196513644996, 213414296541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 214958080 571473920 577044480 ⟨⟨200090586021, 200090586030⟩, ⟨191817961680, 208528808927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 577044480 582615040 ⟨⟨201861337245, 201861337254⟩, ⟨193561560155, 210326648775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 212336640 582615040 588185600 ⟨⟨206670929676, 206670929685⟩, ⟨198276698227, 215231520205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 212336640 588185600 593756160 ⟨⟨208458998336, 208458998345⟩, ⟨200037664123, 217046593505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 214958080 582615040 588185600 ⟨⟨203630024028, 203630024037⟩, ⟨195303121467, 212122392311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212336640 214958080 588185600 593756160 ⟨⟨205396673996, 205396674005⟩, ⟨197042672758, 213916067636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 571473920 577044480 ⟨⟨197112185133, 197112185136⟩, ⟨188906097329, 205482931872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 217579520 577044480 582615040 ⟨⟨198861294726, 198861294730⟩, ⟨190628072591, 207259135502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 571473920 577044480 ⟨⟨194152772018, 194152772026⟩, ⟨186012459243, 202456807361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 220200960 577044480 582615040 ⟨⟨195880180468, 195880180477⟩, ⟨187712761025, 204211305257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214958080 217579520 582615040 588185600 ⟨⟨200608418789, 200608418794⟩, ⟨192348087242, 209033324192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214958080 217579520 588185600 593756160 ⟨⟨202353583725, 202353583729⟩, ⟨194066167229, 210805524782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 220200960 582615040 588185600 ⟨⟨197605680277, 197605680285⟩, ⟨189411176773, 205963867517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217579520 220200960 588185600 593756160 ⟨⟨199329296662, 199329296671⟩, ⟨191107731281, 207714519774⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 571473920 593756160 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 582615040) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 577044480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 577044480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212336640) (by decide) (join_sr (m := 588185600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 588185600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 582615040) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 577044480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 577044480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 217579520) (by decide) (join_sr (m := 588185600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 588185600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (453/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
