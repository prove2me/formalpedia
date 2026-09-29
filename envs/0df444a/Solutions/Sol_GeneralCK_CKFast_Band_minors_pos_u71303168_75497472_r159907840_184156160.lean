-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u71303168_75497472_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:48:52.92397+00:00
-- url     : https://prove2.me/submissions/fd50ce46-fbf0-4726-b4eb-e6f03238e322

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/200, 9/100]`, `ρ ∈ [61/320, 281/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 71303168 72351744 159907840 165969920 ⟨⟨162726288180, 162726288193⟩, ⟨154708212266, 170943646555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 72351744 73400320 159907840 165969920 ⟨⟨161287780148, 161287780162⟩, ⟨153350182945, 169421440135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 71303168 72351744 165969920 172032000 ⟨⟨167533121154, 167533121164⟩, ⟨159507514804, 175754572038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 72351744 73400320 165969920 172032000 ⟨⟨166068924727, 166068924738⟩, ⟨158123075310, 174207513052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 73400320 74448896 159907840 165969920 ⟨⟨159871159017, 159871159030⟩, ⟨152012464135, 167922776555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 74448896 75497472 159907840 165969920 ⟨⟨158475863221, 158475863234⟩, ⟨150694540686, 166447045214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 73400320 74448896 165969920 172032000 ⟨⟨164626666502, 164626666516⟩, ⟨156759032353, 172684009165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 74448896 75497472 165969920 172032000 ⟨⟨163205790615, 163205790628⟩, ⟨155414874868, 171183457278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 71303168 72351744 172032000 178094080 ⟨⟨172278871215, 172278871228⟩, ⟨164246728786, 180503485688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 72351744 73400320 172032000 178094080 ⟨⟨170790053579, 170790053593⟩, ⟨162836936490, 178932647423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 71303168 72351744 178094080 184156160 ⟨⟨176965508174, 176965508185⟩, ⟨168927760385, 185192419672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 72351744 73400320 178094080 184156160 ⟨⟨175453082545, 175453082559⟩, ⟨167493620483, 183598819773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 73400320 74448896 172032000 178094080 ⟨⟨169323206161, 169323206171⟩, ⟨161447607040, 177385357860⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 74448896 75497472 172032000 178094080 ⟨⟨167877779106, 167877779116⟩, ⟨160078233819, 175861021664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 73400320 74448896 178094080 184156160 ⟨⟨173962641470, 173962641480⟩, ⟨166079991587, 182028745172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 74448896 75497472 178094080 184156160 ⟨⟨172493641376, 172493641389⟩, ⟨164686371853, 180481608499⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 71303168 75497472 159907840 184156160 t = true :=
  ⟨_, (join_sr (m := 172032000) (by decide) (join_su (m := 73400320) (by decide) (join_sr (m := 165969920) (by decide) (join_su (m := 72351744) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 72351744) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 165969920) (by decide) (join_su (m := 74448896) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 74448896) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 73400320) (by decide) (join_sr (m := 178094080) (by decide) (join_su (m := 72351744) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 72351744) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178094080) (by decide) (join_su (m := 74448896) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 74448896) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/200 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
