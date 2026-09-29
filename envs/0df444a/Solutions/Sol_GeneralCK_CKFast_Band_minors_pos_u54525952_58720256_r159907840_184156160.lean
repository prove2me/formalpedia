-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u54525952_58720256_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:14:26.907875+00:00
-- url     : https://prove2.me/submissions/291d2939-57db-4ee7-9788-ad44bc9957b1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/200, 7/100]`, `ρ ∈ [61/320, 281/1280]` by 12 cells of the computing
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
theorem cell0 : cellOK 54525952 55574528 159907840 165969920 ⟨⟨189270401070, 189270401085⟩, ⟨179703726220, 199101357980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 55574528 56623104 159907840 165969920 ⟨⟨187384911201, 187384911216⟩, ⟨177932159429, 197096980632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 54525952 55574528 165969920 172032000 ⟨⟨194488410671, 194488410684⟩, ⟨184932215534, 204302827341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 55574528 56623104 165969920 172032000 ⟨⟨192577669797, 192577669809⟩, ⟨183133806886, 202275010911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 56623104 57671680 159907840 165969920 ⟨⟨185533936414, 185533936426⟩, ⟨176192445770, 195129922405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 57671680 58720256 159907840 165969920 ⟨⟨183716424606, 183716424621⟩, ⟨174483626299, 193199032640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 56623104 57671680 165969920 172032000 ⟨⟨190701315361, 190701315374⟩, ⟨181367200459, 200284297710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 57671680 58720256 165969920 172032000 ⟨⟨188858313572, 188858313586⟩, ⟨179631451577, 198329559909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 54525952 56623104 172032000 178094080 ⟨⟨198653766624, 198653766640⟩, ⟨184743193243, 213118994600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 54525952 56623104 178094080 184156160 ⟨⟨203701604936, 203701604951⟩, ⟨189796310036, 218149993339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 56623104 58720256 172032000 178094080 ⟨⟨194852825721, 194852825736⟩, ⟨181248251967, 208993155245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 56623104 58720256 178094080 184156160 ⟨⟨199855300242, 199855300257⟩, ⟨186252018271, 213983588391⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 54525952 58720256 159907840 184156160 t = true :=
  ⟨_, (join_sr (m := 172032000) (by decide) (join_su (m := 56623104) (by decide) (join_sr (m := 165969920) (by decide) (join_su (m := 55574528) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 55574528) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 165969920) (by decide) (join_su (m := 57671680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 57671680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 56623104) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 178094080) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/200 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
