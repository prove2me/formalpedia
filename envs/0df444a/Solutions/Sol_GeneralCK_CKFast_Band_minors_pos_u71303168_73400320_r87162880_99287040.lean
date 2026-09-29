-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u71303168_73400320_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:29:45.596095+00:00
-- url     : https://prove2.me/submissions/8d5bc55c-0d7b-4909-9964-8367b34b9e77

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/200, 7/80]`, `ρ ∈ [133/1280, 303/2560]` by 10 cells of the computing
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
theorem cell0 : cellOK 71303168 71827456 87162880 90193920 ⟨⟨98228610715, 98228610725⟩, ⟨94280587944, 102238733458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 71827456 72351744 87162880 90193920 ⟨⟨97718676772, 97718676775⟩, ⟨93793087184, 101705735405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 71303168 72351744 90193920 93224960 ⟨⟨100863406731, 100863406741⟩, ⟨95086203887, 106774497722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 72351744 72876032 87162880 90193920 ⟨⟨97213553938, 97213553948⟩, ⟨93310135456, 101177820489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 72876032 73400320 87162880 90193920 ⟨⟨96713167572, 96713167582⟩, ⟨92831662770, 100654909183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 72351744 73400320 90193920 93224960 ⟨⟨99830452293, 99830452305⟩, ⟨94115189979, 105677033530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 71303168 72351744 93224960 96256000 ⟨⟨103729672956, 103729672969⟩, ⟨97940845958, 109651341147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 71303168 72351744 96256000 99287040 ⟨⟨106572300932, 106572300944⟩, ⟨100772262109, 112504141248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 72351744 73400320 93224960 96256000 ⟨⟨102674573340, 102674573350⟩, ⟨96947569772, 108531891166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 72351744 73400320 96256000 99287040 ⟨⟨105495584879, 105495584890⟩, ⟨99757242304, 111363243719⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 71303168 73400320 87162880 99287040 t = true :=
  ⟨_, (join_sr (m := 93224960) (by decide) (join_su (m := 72351744) (by decide) (join_sr (m := 90193920) (by decide) (join_su (m := 71827456) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 90193920) (by decide) (join_su (m := 72876032) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 72351744) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 96256000) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/200 : ℝ) (7/80 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e1 : (((73400320 : ℤ) : ℝ) / (D : ℝ)) = (7/80 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
