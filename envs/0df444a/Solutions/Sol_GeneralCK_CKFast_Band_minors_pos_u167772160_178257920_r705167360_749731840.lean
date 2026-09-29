-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r705167360_749731840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:26:59.367077+00:00
-- url     : https://prove2.me/submissions/b3530442-541b-4455-a835-9dc45bbe33b9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [269/320, 143/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 705167360 716308480 ⟨⟨305237074115, 305237074126⟩, ⟨293286122576, 317419554657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 170393600 173015040 705167360 716308480 ⟨⟨301395377267, 301395377278⟩, ⟨289549524664, 313472408457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 170393600 716308480 727449600 ⟨⟨309334734222, 309334734233⟩, ⟨297333500974, 321565119715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 716308480 727449600 ⟨⟨305457463138, 305457463149⟩, ⟨293560722584, 317583121031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 175636480 705167360 716308480 ⟨⟨297578277883, 297578277894⟩, ⟨285836566890, 309550773013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 175636480 178257920 705167360 716308480 ⟨⟨293785236330, 293785236336⟩, ⟨282146725039, 305654095149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 173015040 175636480 716308480 727449600 ⟨⟨301604459439, 301604459450⟩, ⟨289811292939, 313626261667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 175636480 178257920 716308480 727449600 ⟨⟨297775193489, 297775193496⟩, ⟨286084696777, 309693999515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 170393600 727449600 738590720 ⟨⟨313422624834, 313422624844⟩, ⟨301371318436, 325700682926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 173015040 727449600 738590720 ⟨⟨309510054348, 309510054360⟩, ⟨297562628631, 321684111913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 170393600 738590720 749731840 ⟨⟨317501105386, 317501105396⟩, ⟨305399924978, 329826612789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 170393600 173015040 738590720 749731840 ⟨⟨313553498209, 313553498220⟩, ⟨301555581031, 325775737157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 727449600 738590720 ⟨⟨305621417594, 305621417605⟩, ⟨293776992305, 317692305580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 178257920 727449600 738590720 ⟨⟨301756194817, 301756194824⟩, ⟨290013903062, 313724732744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 173015040 175636480 738590720 749731840 ⟨⟨309629487815, 309629487825⟩, ⟨297733991703, 321749248647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 738590720 749731840 ⟨⟨305728564214, 305728564219⟩, ⟨293934659376, 317746626854⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 705167360 749731840 t = true :=
  ⟨_, (join_sr (m := 727449600) (by decide) (join_su (m := 173015040) (by decide) (join_sr (m := 716308480) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 170393600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 716308480) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 175636480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 173015040) (by decide) (join_sr (m := 738590720) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 170393600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 738590720) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 175636480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (269/320 : ℝ) (143/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  have e3 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
