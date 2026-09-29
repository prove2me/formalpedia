-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u71303168_75497472_r123535360_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:42:56.393993+00:00
-- url     : https://prove2.me/submissions/5b34c8cc-876c-4804-bed9-95a9289e6b64

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/200, 9/100]`, `ρ ∈ [377/2560, 207/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 71303168 72351744 123535360 126566400 ⟨⟨131163110420, 131163110433⟩, ⟨125278595000, 137170405668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 71303168 72351744 126566400 129597440 ⟨⟨133792394089, 133792394102⟩, ⟨127900107018, 139806496417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 72351744 73400320 123535360 126566400 ⟨⟨129913238758, 129913238771⟩, ⟨124088905990, 135858215604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 72351744 73400320 126566400 129597440 ⟨⟨132525419896, 132525419910⟩, ⟨126693114406, 138477440937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 71303168 72351744 129597440 132628480 ⟨⟨136402421786, 136402421796⟩, ⟨130502648309, 142423053547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 71303168 72351744 132628480 135659520 ⟨⟨138993534683, 138993534693⟩, ⟨133086550870, 145020427399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 72351744 73400320 129597440 132628480 ⟨⟨135118729280, 135118729293⟩, ⟨129278731123, 141077521521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 72351744 73400320 132628480 135659520 ⟨⟨137693497479, 137693497490⟩, ⟨131846077855, 143658796783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 73400320 74448896 123535360 126566400 ⟨⟨128684372587, 128684372597⟩, ⟨122918922711, 134568390128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 73400320 74448896 126566400 129597440 ⟨⟨131279564903, 131279564913⟩, ⟨125505953758, 137170849694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 74448896 75497472 123535360 126566400 ⟨⟨127475926233, 127475926243⟩, ⟨121768101380, 133300299467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 74448896 75497472 126566400 129597440 ⟨⟨130054244351, 130054244361⟩, ⟨124338081535, 135886094583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 73400320 74448896 129597440 132628480 ⟨⟨133856260989, 133856260999⟩, ⟨128074763470, 139754544696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 73400320 74448896 132628480 135659520 ⟨⟨136414781187, 136414781197⟩, ⟨130625663643, 142319804027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 74448896 75497472 129597440 132628480 ⟨⟨132614433293, 132614433306⟩, ⟨126890202281, 138453496849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 74448896 75497472 132628480 135659520 ⟨⟨135156803534, 135156803544⟩, ⟨129424765851, 141002824990⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 71303168 75497472 123535360 135659520 t = true :=
  ⟨_, (join_su (m := 73400320) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 72351744) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126566400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 72351744) (by decide) (join_sr (m := 132628480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 132628480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 129597440) (by decide) (join_su (m := 74448896) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126566400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 74448896) (by decide) (join_sr (m := 132628480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 132628480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/200 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (377/2560 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
