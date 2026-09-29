-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_62914560_r123535360_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:11:16.456715+00:00
-- url     : https://prove2.me/submissions/e44f31c6-7d2f-4a58-a66a-68a71f6f54cf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 3/40]`, `ρ ∈ [377/2560, 207/1280]` by 12 cells of the computing
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
theorem cell0 : cellOK 58720256 59768832 123535360 126566400 ⟨⟨148048938174, 148048938186⟩, ⟨141322684295, 154929209788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 58720256 59768832 126566400 129597440 ⟨⟨150891663318, 150891663329⟩, ⟨144161341587, 157774449930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 59768832 60817408 123535360 126566400 ⟨⟨146491485168, 146491485180⟩, ⟨139845083647, 153288835811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 59768832 60817408 126566400 129597440 ⟨⟨149315905970, 149315905984⟩, ⟨142665013533, 156116257388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 58720256 59768832 129597440 135659520 ⟨⟨155109723290, 155109723302⟩, ⟨145979765919, 164513221685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 59768832 60817408 129597440 135659520 ⟨⟨153507456201, 153507456216⟩, ⟨144487748015, 162795221715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 60817408 61865984 123535360 126566400 ⟨⟨144964284262, 144964284276⟩, ⟨138395749943, 151680795908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 60817408 61865984 126566400 129597440 ⟨⟨147770482118, 147770482132⟩, ⟨141197058839, 154490452319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 61865984 62914560 123535360 126566400 ⟨⟨143466371793, 143466371807⟩, ⟨136973792887, 150104048944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 61865984 62914560 126566400 129597440 ⟨⟨146254432893, 146254432905⟩, ⟨139756590543, 152896000006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 60817408 61865984 129597440 135659520 ⟨⟨151935622862, 151935622876⟩, ⟨143023514030, 161110473871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 61865984 62914560 129597440 135659520 ⟨⟨150393272107, 150393272119⟩, ⟨141586208040, 159457924822⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 62914560 123535360 135659520 t = true :=
  ⟨_, (join_su (m := 60817408) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 59768832) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126566400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 59768832) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 129597440) (by decide) (join_su (m := 61865984) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 126566400) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 61865984) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (3/40 : ℝ) →
    rho ∈ Set.Icc (377/2560 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e2 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
