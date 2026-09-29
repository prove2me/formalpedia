-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u201850880_204472320_r192675840_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:16:56.955505+00:00
-- url     : https://prove2.me/submissions/92872452-14d4-48f5-a40f-050130dda6d5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [77/320, 39/160]`, `ρ ∈ [147/640, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 201850880 202506240 192675840 195461120 ⟨⟨78179090567, 78179090575⟩, ⟨76188410243, 80185394476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 202506240 203161600 192675840 195461120 ⟨⟨77852010301, 77852010307⟩, ⟨75866938775, 79852636797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 202506240 195461120 198246400 ⟨⟨79243918424, 79243918430⟩, ⟨77248905808, 81254554607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 202506240 203161600 195461120 198246400 ⟨⟨78912818071, 78912818077⟩, ⟨76923424444, 80917766910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 203161600 203816960 192675840 195461120 ⟨⟨77526017669, 77526017676⟩, ⟨75546526139, 79520996039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 203816960 204472320 192675840 195461120 ⟨⟨77201104269, 77201104275⟩, ⟨75227164165, 79190463556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 203161600 203816960 195461120 198246400 ⟨⟨78582813828, 78582813836⟩, ⟨76599010405, 80582104587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203816960 204472320 195461120 198246400 ⟨⟨78253897248, 78253897255⟩, ⟨76275655477, 80247558950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 201850880 202506240 198246400 201031680 ⟨⟨80307342603, 80307342610⟩, ⟨78308006260, 82322302395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 202506240 203161600 198246400 201031680 ⟨⟨79972237919, 79972237927⟩, ⟨77978530610, 81981500583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 201850880 202506240 201031680 203816960 ⟨⟨81369371140, 81369371147⟩, ⟨79365719575, 83388645930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 202506240 203161600 201031680 203816960 ⟨⟨81030277761, 81030277768⟩, ⟨79032265130, 83043845783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 203161600 203816960 198246400 201031680 ⟨⟨79638237670, 79638237676⟩, ⟨77650130627, 81641832443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203816960 204472320 198246400 201031680 ⟨⟨79305333362, 79305333368⟩, ⟨77322798054, 81303289246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203161600 203816960 201031680 203816960 ⟨⟨80692296990, 80692296996⟩, ⟨78699894544, 82700187457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203816960 204472320 201031680 203816960 ⟨⟨80355420291, 80355420298⟩, ⟨78368599524, 82357662180⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 201850880 204472320 192675840 203816960 t = true :=
  ⟨_, (join_sr (m := 198246400) (by decide) (join_su (m := 203161600) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 202506240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 202506240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 195461120) (by decide) (join_su (m := 203816960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 203816960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 203161600) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 202506240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 202506240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 201031680) (by decide) (join_su (m := 203816960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 203816960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (77/320 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
