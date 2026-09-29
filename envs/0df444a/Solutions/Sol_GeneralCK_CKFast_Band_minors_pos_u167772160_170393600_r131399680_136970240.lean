-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_170393600_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:59.398178+00:00
-- url     : https://prove2.me/submissions/b1a3c75b-eab5-4092-8b90-d2dd8f85c477

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 13/64]`, `ρ ∈ [401/2560, 209/1280]` by 9 cells of the computing
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
theorem cell0 : cellOK 167772160 168427520 131399680 134184960 ⟨⟨67956732564, 67956732570⟩, ⟨65738795305, 70195076179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 168427520 169082880 131399680 134184960 ⟨⟨67665802369, 67665802373⟩, ⟨65455134602, 69896762421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 168427520 134184960 136970240 ⟨⟨69302447607, 69302447613⟩, ⟨67079237534, 71546046798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 168427520 169082880 134184960 136970240 ⟨⟨69006352676, 69006352678⟩, ⟨66790426321, 71242554635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 169082880 169738240 131399680 134184960 ⟨⟨67376224943, 67376224951⟩, ⟨65172779771, 69599849357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 169738240 170393600 131399680 132792320 ⟨⟨66754980773, 66754980781⟩, ⟨64963072240, 68560030668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 169738240 170393600 132792320 134184960 ⟨⟨67420818961, 67420818967⟩, ⟨65626566589, 69228211283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 169082880 169738240 134184960 136970240 ⟨⟨68711627920, 68711627927⟩, ⟨66502938402, 70940480547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 169738240 170393600 134184960 136970240 ⟨⟨68418260715, 68418260721⟩, ⟨66216761620, 70639811416⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 170393600 131399680 136970240 t = true :=
  ⟨_, (join_su (m := 169082880) (by decide) (join_sr (m := 134184960) (by decide) (join_su (m := 168427520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 168427520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134184960) (by decide) (join_su (m := 169738240) (by decide) (leaf_ok cell4) (join_sr (m := 132792320) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 169738240) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (13/64 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
