-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u54525952_58720256_r123535360_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:08:42.955427+00:00
-- url     : https://prove2.me/submissions/202e39c0-188f-4972-b38f-900e807ae7d2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/200, 7/100]`, `ρ ∈ [377/2560, 207/1280]` by 8 cells of the computing
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
theorem cell0 : cellOK 54525952 55574528 123535360 129597440 ⟨⟨156063853289, 156063853301⟩, ⟨146462640000, 165969575705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 55574528 56623104 123535360 129597440 ⟨⟨154365474530, 154365474542⟩, ⟨144887734221, 164141197528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 54525952 55574528 129597440 135659520 ⟨⟨161843705802, 161843705817⟩, ⟨152244174611, 171740550668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 55574528 56623104 129597440 135659520 ⟨⟨160109296509, 160109296521⟩, ⟨150631666638, 169878004921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 56623104 57671680 123535360 129597440 ⟨⟨152701701614, 152701701630⟩, ⟨143344262744, 162350811170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 57671680 58720256 123535360 129597440 ⟨⟨151071381094, 151071381105⟩, ⟨141831193722, 160597132144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 56623104 57671680 129597440 135659520 ⟨⟨158409580066, 158409580081⟩, ⟨149050769683, 168053434161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 57671680 58720256 129597440 135659520 ⟨⟨156743418127, 156743418141⟩, ⟨147500461729, 166265575110⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 54525952 58720256 123535360 135659520 t = true :=
  ⟨_, (join_su (m := 56623104) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 55574528) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 55574528) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 129597440) (by decide) (join_su (m := 57671680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 57671680) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/200 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (377/2560 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
