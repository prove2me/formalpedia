-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r382074880_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:02:45.279563+00:00
-- url     : https://prove2.me/submissions/c2d06ed7-f90d-4156-a894-e984a25dc63e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [583/1280, 15/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 382074880 384860160 ⟨⟨115496100836, 115496100843⟩, ⟨112136339139, 118892978937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 242483200 384860160 387645440 ⟨⟨116291934551, 116291934557⟩, ⟨112925454082, 119695564222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 243793920 382074880 384860160 ⟨⟨114496831625, 114496831633⟩, ⟨111150789265, 117879815853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 384860160 387645440 ⟨⟨115286480790, 115286480796⟩, ⟨111933741283, 118676195735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 242483200 387645440 390430720 ⟨⟨117087280140, 117087280146⟩, ⟨113714082517, 120497659584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 242483200 390430720 393216000 ⟨⟨117882140119, 117882140125⟩, ⟨114502226946, 121299267552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243793920 387645440 390430720 ⟨⟨116075653368, 116075653376⟩, ⟨112716218175, 119472097397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242483200 243793920 390430720 393216000 ⟨⟨116864351809, 116864351817⟩, ⟨113498222373, 120267523298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 245104640 382074880 384860160 ⟨⟨113501295087, 113501295094⟩, ⟨110168870599, 116870488440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 243793920 245104640 384860160 387645440 ⟨⟨114284765694, 114284765700⟩, ⟨110945665933, 117660668645⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 246415360 382074880 384860160 ⟨⟨112509443662, 112509443665⟩, ⟨109190536776, 115864947920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245104640 246415360 384860160 387645440 ⟨⟨113286741707, 113286741709⟩, ⟨109961181662, 116648934187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 387645440 390430720 ⟨⟨115067771055, 115067771063⟩, ⟨111721997323, 118450382131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243793920 245104640 390430720 393216000 ⟨⟨115850313549, 115850313557⟩, ⟨112497867139, 119239631286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 246415360 387645440 390430720 ⟨⟨114063585647, 114063585650⟩, ⟨110731373595, 117432465029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 390430720 393216000 ⟨⟨114839977794, 114839977798⟩, ⟨111501114874, 118215542771⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 382074880 393216000 t = true :=
  ⟨_, (join_su (m := 243793920) (by decide) (join_sr (m := 387645440) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 384860160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 384860160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 242483200) (by decide) (join_sr (m := 390430720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 390430720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 387645440) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 384860160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 384860160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245104640) (by decide) (join_sr (m := 390430720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 390430720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (583/1280 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((382074880 : ℤ) : ℝ) / (D : ℝ)) = (583/1280 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
