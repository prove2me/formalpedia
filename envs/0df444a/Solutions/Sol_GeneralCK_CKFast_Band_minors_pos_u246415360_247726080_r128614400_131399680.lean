-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_247726080_r128614400_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:41:19.783082+00:00
-- url     : https://prove2.me/submissions/320864f7-0af4-4ec0-af59-613b44b8fb49

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 189/640]`, `ρ ∈ [157/1024, 401/2560]` by 10 cells of the computing
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
theorem cell0 : cellOK 246415360 246743040 128614400 130007040 ⟨⟨39111617354, 39111617356⟩, ⟨38319693726, 39906442234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246743040 247070720 128614400 130007040 ⟨⟨39019274695, 39019274701⟩, ⟨38228312817, 39813132062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 246743040 130007040 131399680 ⟨⟨39524125743, 39524125745⟩, ⟨38731283035, 40319871207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 246743040 247070720 130007040 131399680 ⟨⟨39430847778, 39430847783⟩, ⟨38638968296, 40225624256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247070720 247398400 128614400 129310720 ⟨⟨38824369978, 38824369983⟩, ⟨38148169032, 39502601535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247070720 247398400 129310720 130007040 ⟨⟨39029732044, 39029732049⟩, ⟨38353107295, 39708388173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247398400 247726080 128614400 129310720 ⟨⟨38732508975, 38732508980⟩, ⟨38056974065, 39410071133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247398400 247726080 129310720 130007040 ⟨⟨38937404105, 38937404110⟩, ⟨38261446003, 39615390228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247070720 247398400 130007040 131399680 ⟨⟨39337695129, 39337695135⟩, ⟨38546776766, 40131504744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247398400 247726080 130007040 131399680 ⟨⟨39244667323, 39244667329⟩, ⟨38454707977, 40037512195⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 247726080 128614400 131399680 t = true :=
  ⟨_, (join_su (m := 247070720) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 246743040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 130007040) (by decide) (join_su (m := 247398400) (by decide) (join_sr (m := 129310720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 129310720) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 247398400) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (189/640 : ℝ) →
    rho ∈ Set.Icc (157/1024 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e2 : (((128614400 : ℤ) : ℝ) / (D : ℝ)) = (157/1024 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
