-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r638320640_660602880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:59:14.945591+00:00
-- url     : https://prove2.me/submissions/a0cf9dd4-aa68-4e7b-a856-292a4063071f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [487/640, 63/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 638320640 643891200 ⟨⟨224461048544, 224461048553⟩, ⟨215797018069, 233290243091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 212336640 643891200 649461760 ⟨⟨226229500465, 226229500474⟩, ⟨217538631088, 235085388027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 214958080 638320640 643891200 ⟨⟨221209338456, 221209338466⟩, ⟨212612576172, 229970623780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 643891200 649461760 ⟨⟨222957101433, 222957101442⟩, ⟨214333482313, 231745123460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 212336640 649461760 655032320 ⟨⟨227996141622, 227996141632⟩, ⟨219278457007, 236878693675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 212336640 655032320 660602880 ⟨⟨229760998775, 229760998785⟩, ⟨221016522101, 238670187265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 214958080 649461760 655032320 ⟨⟨224703120174, 224703120183⟩, ⟨216052665840, 233517852517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212336640 214958080 655032320 660602880 ⟨⟨226447420312, 226447420321⟩, ⟨217770151930, 235288837025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 638320640 643891200 ⟨⟨217976182399, 217976182403⟩, ⟨209446028585, 226670212227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 217579520 643891200 649461760 ⟨⟨219703172390, 219703172394⟩, ⟨211146153805, 228423971886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 638320640 643891200 ⟨⟨214761175638, 214761175647⟩, ⟨206296982516, 223388592190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 220200960 643891200 649461760 ⟨⟨216467311559, 216467311569⟩, ⟨207976255453, 225121520319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214958080 217579520 649461760 655032320 ⟨⟨221428483117, 221428483121⟩, ⟨212844619373, 230176028005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214958080 217579520 655032320 660602880 ⟨⟨223152139123, 223152139126⟩, ⟨214541449399, 231926405541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 220200960 649461760 655032320 ⟨⟨218171831641, 218171831650⟩, ⟨209653930178, 226852810413⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217579520 220200960 655032320 660602880 ⟨⟨219874759370, 219874759379⟩, ⟨211330029774, 228582486351⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 638320640 660602880 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 649461760) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 643891200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 643891200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212336640) (by decide) (join_sr (m := 655032320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 655032320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 649461760) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 643891200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 643891200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 217579520) (by decide) (join_sr (m := 655032320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 655032320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (487/640 : ℝ) (63/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((638320640 : ℤ) : ℝ) / (D : ℝ)) = (487/640 : ℝ) := by norm_num [D]
  have e3 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
