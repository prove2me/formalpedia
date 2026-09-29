-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_60817408_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:03:20.120574+00:00
-- url     : https://prove2.me/submissions/0a6859ea-14dd-4c9c-bd98-51e7c7cac1e2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 29/400]`, `ρ ∈ [3/40, 229/2560]` by 17 cells of the computing
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
theorem cell0 : cellOK 58720256 59244544 62914560 65945600 ⟨⟨85360469883, 85360469890⟩, ⟨80834249193, 89975318248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 59244544 59768832 62914560 65945600 ⟨⟨84828084961, 84828084972⟩, ⟨80333165601, 89410502204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 58720256 59244544 65945600 68976640 ⟨⟨88837640275, 88837640283⟩, ⟨84302934098, 93459965617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 59244544 59768832 65945600 68976640 ⟨⟨88288492136, 88288492147⟩, ⟨83785010019, 92878487530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 59768832 60293120 62914560 65945600 ⟨⟨84302087873, 84302087886⟩, ⟨79838015753, 88852550426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 60293120 60817408 62914560 64430080 ⟨⟨82919576707, 82919576718⟩, ⟨79680741543, 86204349090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 60293120 60817408 64430080 65945600 ⟨⟨84642734851, 84642734862⟩, ⟨81400055440, 87931123188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 59768832 60293120 65945600 68976640 ⟨⟨87745863437, 87745863451⟩, ⟨83273155545, 92304000372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 60293120 60817408 65945600 68976640 ⟨⟨87209629265, 87209629276⟩, ⟨82767255564, 91736368852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 58720256 59244544 68976640 72007680 ⟨⟨92275802950, 92275802958⟩, ⟨87733184908, 96905043656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 59244544 59768832 68976640 72007680 ⟨⟨91710419341, 91710419353⟩, ⟨87198939304, 96307439586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 58720256 59244544 72007680 75038720 ⟨⟨95675912895, 95675912897⟩, ⟨91125930378, 100311533577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 59244544 59768832 72007680 75038720 ⟨⟨95094801478, 95094801489⟩, ⟨90575862778, 99698318844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 59768832 60293120 68976640 72007680 ⟨⟨91151677694, 91151677708⟩, ⟨86670890208, 95716943905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 60293120 60817408 68976640 72007680 ⟨⟨90599451954, 90599451965⟩, ⟨86148921206, 95133420375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 59768832 60293120 72007680 75038720 ⟨⟨94520445969, 94520445981⟩, ⟨90032110137, 99092321284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 60293120 60817408 72007680 75038720 ⟨⟨93952719344, 93952719355⟩, ⟨89494554902, 98493403887⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 60817408 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 59768832) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 59244544) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 59244544) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 60293120) (by decide) (leaf_ok cell4) (join_sr (m := 64430080) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 60293120) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 59768832) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 59244544) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 59244544) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 72007680) (by decide) (join_su (m := 60293120) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 60293120) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (29/400 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((60817408 : ℤ) : ℝ) / (D : ℝ)) = (29/400 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
