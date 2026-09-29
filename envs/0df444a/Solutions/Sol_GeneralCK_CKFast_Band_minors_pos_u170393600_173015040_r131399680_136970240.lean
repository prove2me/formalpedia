-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u170393600_173015040_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:33.421404+00:00
-- url     : https://prove2.me/submissions/60017008-9edd-47d0-9596-35bd67182462

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/64, 33/160]`, `ρ ∈ [401/2560, 209/1280]` by 12 cells of the computing
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
theorem cell0 : cellOK 170393600 171048960 131399680 132792320 ⟨⟨66469354632, 66469354640⟩, ⟨64682605835, 68269179289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 170393600 171048960 132792320 134184960 ⟨⟨67132628522, 67132628530⟩, ⟨65343541888, 68934789753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 171048960 171704320 131399680 132792320 ⟨⟨66185039849, 66185039856⟩, ⟨64403416502, 67979674134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 171048960 171704320 132792320 134184960 ⟨⟨66845758055, 66845758061⟩, ⟨65061802871, 68642723058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 170393600 171048960 134184960 136970240 ⟨⟨68126238573, 68126238579⟩, ⟨65931883959, 70340534279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 171048960 171704320 134184960 136970240 ⟨⟨67835549165, 67835549171⟩, ⟨65648293552, 70042636330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 171704320 172359680 131399680 132792320 ⟨⟨65902024383, 65902024385⟩, ⟨64125492540, 67691502812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 171704320 172359680 132792320 134184960 ⟨⟨66560195458, 66560195462⟩, ⟨64781337782, 68351998744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 172359680 173015040 131399680 132792320 ⟨⟨65620296327, 65620296334⟩, ⟨63848822390, 67404653074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 172359680 173015040 132792320 134184960 ⟨⟨66275928768, 66275928776⟩, ⟨64502134998, 68062604509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 171704320 172359680 134184960 136970240 ⟨⟨67546180302, 67546180304⟩, ⟨65365978665, 69746104911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 172359680 173015040 134184960 136970240 ⟨⟨67258119935, 67258119941⟩, ⟨65084927706, 69450927518⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 170393600 173015040 131399680 136970240 t = true :=
  ⟨_, (join_su (m := 171704320) (by decide) (join_sr (m := 134184960) (by decide) (join_su (m := 171048960) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 132792320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 171048960) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 134184960) (by decide) (join_su (m := 172359680) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 132792320) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 172359680) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/64 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
