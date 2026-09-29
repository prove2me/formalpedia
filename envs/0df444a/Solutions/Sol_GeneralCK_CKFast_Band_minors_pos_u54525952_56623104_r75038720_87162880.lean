-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u54525952_56623104_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:59:17.60815+00:00
-- url     : https://prove2.me/submissions/68cd8b82-7dab-4959-a4a5-9b91d826ec80

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/200, 27/400]`, `ρ ∈ [229/2560, 133/1280]` by 12 cells of the computing
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
theorem cell0 : cellOK 54525952 55050240 75038720 78069760 ⟨⟨104073212334, 104073212348⟩, ⟨99251932477, 108988229489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 55050240 55574528 75038720 78069760 ⟨⟨103416941754, 103416941766⟩, ⟨98630464260, 108295941620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 54525952 55050240 78069760 81100800 ⟨⟨107521711912, 107521711927⟩, ⟨102695150565, 112440848810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 55050240 55574528 78069760 81100800 ⟨⟨106849865712, 106849865724⟩, ⟨102057953293, 111733166566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 55574528 56098816 75038720 78069760 ⟨⟨102768685411, 102768685423⟩, ⟨98016488886, 107612213782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 56098816 56623104 75038720 78069760 ⟨⟨102128285421, 102128285436⟩, ⟨97409860248, 106936875667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 55574528 56098816 78069760 81100800 ⟨⟨106186136428, 106186136442⟩, ⟨101428357934, 111034139832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 56098816 56623104 78069760 81100800 ⟨⟨105530365699, 105530365714⟩, ⟨100806217640, 110343598096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 54525952 55574528 81100800 84131840 ⟨⟨110586444192, 110586444206⟩, ⟨103597887636, 117770742483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 54525952 55574528 84131840 87162880 ⟨⟨113950077501, 113950077516⟩, ⟨106952128334, 121141568448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 55574528 56623104 81100800 84131840 ⟨⟨109229015437, 109229015449⟩, ⟨102335810219, 116313192673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 55574528 56623104 84131840 87162880 ⟨⟨112563693969, 112563693981⟩, ⟨105660694586, 119655569278⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 54525952 56623104 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 55574528) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 55050240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 55050240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 56098816) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 56098816) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 55574528) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 84131840) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/200 : ℝ) (27/400 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e1 : (((56623104 : ℤ) : ℝ) / (D : ℝ)) = (27/400 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
