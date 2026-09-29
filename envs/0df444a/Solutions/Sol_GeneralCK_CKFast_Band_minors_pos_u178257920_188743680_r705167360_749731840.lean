-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r705167360_749731840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:26:59.081156+00:00
-- url     : https://prove2.me/submissions/570037b5-81ec-471a-aff6-3d49a4da3bdf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [269/320, 143/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 705167360 716308480 ⟨⟨290015727351, 290015727364⟩, ⟨278479488867, 301781836409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 180879360 183500800 705167360 716308480 ⟨⟨286269239481, 286269239491⟩, ⟨274834361508, 297933472432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 180879360 716308480 727449600 ⟨⟨293969149700, 293969149713⟩, ⟨282380432499, 305785806844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 716308480 727449600 ⟨⟨290185825958, 290185825970⟩, ⟨278698011610, 301901169666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 186122240 705167360 716308480 ⟨⟨282545274437, 282545274448⟩, ⟨271210858920, 294108492358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 186122240 188743680 705167360 716308480 ⟨⟨278843346602, 278843346612⟩, ⟨267608509365, 290306398269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 183500800 186122240 716308480 727449600 ⟨⟨286424733036, 286424733048⟩, ⟨275036958154, 298039587170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 186122240 188743680 716308480 727449600 ⟨⟨282685394075, 282685394087⟩, ⟨271396808219, 294200571174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 180879360 727449600 738590720 ⟨⟨297913879992, 297913880003⟩, ⟨286272867881, 309780876254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 183500800 727449600 738590720 ⟨⟨294093980262, 294093980272⟩, ⟨282553406565, 305860232373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 180879360 738590720 749731840 ⟨⟨301850230839, 301850230850⟩, ⟨290157099532, 313767365062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 180879360 183500800 738590720 749731840 ⟨⟨297994003996, 297994004006⟩, ⟨286400840200, 309810969655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 727449600 738590720 ⟨⟨290296015370, 290296015380⟩, ⟨278855051189, 301962310219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 188743680 727449600 738590720 ⟨⟨286519517136, 286519517147⟩, ⟨275177345613, 298086631236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 183500800 186122240 738590720 749731840 ⟨⟨294159412301, 294159412311⟩, ⟨282665421428, 305876959566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 738590720 749731840 ⟨⟨290345996183, 290345996193⟩, ⟨278950394794, 301964865751⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 705167360 749731840 t = true :=
  ⟨_, (join_sr (m := 727449600) (by decide) (join_su (m := 183500800) (by decide) (join_sr (m := 716308480) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 180879360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 716308480) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 186122240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 183500800) (by decide) (join_sr (m := 738590720) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 180879360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 738590720) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 186122240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (269/320 : ℝ) (143/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  have e3 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
