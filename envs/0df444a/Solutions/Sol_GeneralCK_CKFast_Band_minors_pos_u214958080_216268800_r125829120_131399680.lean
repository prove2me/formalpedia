-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_216268800_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:15:52.949896+00:00
-- url     : https://prove2.me/submissions/d02f839f-5383-4331-8910-8b9790aefeff

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 33/128]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 215285760 125829120 127221760 ⟨⟨47618916507, 47618916513⟩, ⟨46725669814, 48515717912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 215285760 215613440 125829120 127221760 ⟨⟨47514216605, 47514216608⟩, ⟨46622173025, 48409806847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 215285760 127221760 128614400 ⟨⟨48127081308, 48127081314⟩, ⟨47232762513, 49024955636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 215285760 215613440 127221760 128614400 ⟨⟨48021328464, 48021328466⟩, ⟨47128214470, 48917989950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 215613440 215941120 125829120 127221760 ⟨⟨47409694260, 47409694266⟩, ⟨46518850735, 48304076432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 215941120 216268800 125829120 127221760 ⟨⟨47305348764, 47305348771⟩, ⟨46415702251, 48198525937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 215613440 215941120 127221760 128614400 ⟨⟨47915754577, 47915754582⟩, ⟨47023842327, 48811206315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 215941120 216268800 127221760 128614400 ⟨⟨47810358938, 47810358943⟩, ⟨46919645386, 48704604000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 215285760 128614400 130007040 ⟨⟨48634926704, 48634926711⟩, ⟨47739536678, 49533873080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 215285760 215613440 128614400 130007040 ⟨⟨48528122852, 48528122855⟩, ⟨47633939308, 49425854716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 215285760 130007040 131399680 ⟨⟨49142453550, 49142453555⟩, ⟨48245993159, 50042471100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 215285760 215613440 130007040 131399680 ⟨⟨49034600619, 49034600621⟩, ⟨48139348383, 49933401993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 215613440 215941120 128614400 130007040 ⟨⟨48421499349, 48421499355⟩, ⟨47528519228, 49318019796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 215941120 216268800 128614400 130007040 ⟨⟨48315055481, 48315055488⟩, ⟨47423275736, 49210367585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 215613440 215941120 130007040 131399680 ⟨⟨48926929417, 48926929424⟩, ⟨48032882275, 49824517716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 215941120 216268800 130007040 131399680 ⟨⟨48819439229, 48819439234⟩, ⟨47926594131, 49715817525⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 216268800 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 215613440) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 215285760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 215285760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 215941120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 215941120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 215613440) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 215285760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 215285760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 215941120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 215941120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (33/128 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((216268800 : ℤ) : ℝ) / (D : ℝ)) = (33/128 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
