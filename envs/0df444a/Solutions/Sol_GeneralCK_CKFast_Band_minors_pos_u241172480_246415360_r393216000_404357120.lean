-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r393216000_404357120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:12:46.304124+00:00
-- url     : https://prove2.me/submissions/aaf65549-21a6-4ce1-8d77-e07688488df8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [15/32, 617/1280]` by 15 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 393216000 396001280 ⟨⟨118676516997, 118676517003⟩, ⟨115289889866, 122100390647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 242483200 396001280 398786560 ⟨⟨119470413274, 119470413282⟩, ⟨116077073761, 122901031384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 243793920 393216000 396001280 ⟨⟨117652578551, 117652578557⟩, ⟨114279756306, 121062475891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 396001280 398786560 ⟨⟨118440336024, 118440336030⟩, ⟨115060822390, 121856957617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 242483200 398786560 404357120 ⟨⟨120660362016, 120660362022⟩, ⟨116739865769, 124632130100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 242483200 243793920 398786560 401571840 ⟨⟨119227626651, 119227626658⟩, ⟨115841423036, 122650970914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243793920 401571840 404357120 ⟨⟨120014452850, 120014452858⟩, ⟨116621560649, 123444518209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243793920 245104640 393216000 396001280 ⟨⟨116632395547, 116632395555⟩, ⟨113273277736, 120028418493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 245104640 396001280 398786560 ⟨⟨117414019413, 117414019419⟩, ⟨114048231468, 120816746128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245104640 246415360 393216000 396001280 ⟨⟨115615920453, 115615920457⟩, ⟨112270407792, 118998169728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 246415360 396001280 398786560 ⟨⟨116391415921, 116391415925⟩, ⟨113039254635, 119780348210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 243793920 245104640 398786560 401571840 ⟨⟨118195187502, 118195187508⟩, ⟨114822730677, 121604616558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 401571840 404357120 ⟨⟨118975902163, 118975902170⟩, ⟨115596777702, 122392032145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 246415360 398786560 401571840 ⟨⟨117166466489, 117166466491⟩, ⟨113807657683, 120562080515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 246415360 401571840 404357120 ⟨⟨117941074438, 117941074441⟩, ⟨114575619207, 121343368941⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 393216000 404357120 t = true :=
  ⟨_, (join_su (m := 243793920) (by decide) (join_sr (m := 398786560) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 396001280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 396001280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 242483200) (by decide) (leaf_ok cell4) (join_sr (m := 401571840) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 398786560) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 396001280) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 396001280) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 245104640) (by decide) (join_sr (m := 401571840) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 401571840) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (617/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((404357120 : ℤ) : ℝ) / (D : ℝ)) = (617/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
