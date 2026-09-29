-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_75497472_r281149440_305397760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:55:27.154145+00:00
-- url     : https://prove2.me/submissions/ceb8f5ce-42f3-4312-bff3-39e326176963

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 9/100]`, `ρ ∈ [429/1280, 233/640]` by 8 cells of the computing
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
theorem cell0 : cellOK 67108864 69206016 281149440 293273600 ⟨⟨257582228362, 257582228374⟩, ⟨241187579828, 274559466216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 69206016 71303168 281149440 293273600 ⟨⟨253845021329, 253845021340⟩, ⟨237720374374, 270539807237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 69206016 293273600 305397760 ⟨⟨265355376438, 265355376450⟩, ⟨248983040270, 282289962137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69206016 71303168 293273600 305397760 ⟨⟨261574450194, 261574450208⟩, ⟨245466096473, 278233608532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 71303168 73400320 281149440 293273600 ⟨⟨250194388606, 250194388619⟩, ⟨234331572932, 266615267669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 73400320 75497472 281149440 293273600 ⟨⟨246626738784, 246626738797⟩, ⟨231017962468, 262781864614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 71303168 73400320 293273600 305397760 ⟨⟨257878851581, 257878851595⟩, ⟨242026695297, 274270689136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 73400320 75497472 293273600 305397760 ⟨⟨254265102439, 254265102453⟩, ⟨238661711660, 270397362814⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 75497472 281149440 305397760 t = true :=
  ⟨_, (join_su (m := 71303168) (by decide) (join_sr (m := 293273600) (by decide) (join_su (m := 69206016) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 69206016) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 293273600) (by decide) (join_su (m := 73400320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 73400320) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (429/1280 : ℝ) (233/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((281149440 : ℤ) : ℝ) / (D : ℝ)) = (429/1280 : ℝ) := by norm_num [D]
  have e3 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
