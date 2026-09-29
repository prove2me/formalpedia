-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_221511680_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:42:47.036286+00:00
-- url     : https://prove2.me/submissions/b13a7489-55fb-4cef-8e91-3796c4d40d36

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 169/640]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 220528640 131399680 132792320 ⟨⟨47928832298, 47928832299⟩, ⟨47050298705, 48810799182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220528640 220856320 131399680 132792320 ⟨⟨47822776405, 47822776412⟩, ⟨46945405075, 48703573476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 220528640 132792320 134184960 ⟨⟨48419161588, 48419161591⟩, ⟨47539585620, 49302171809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 220528640 220856320 132792320 134184960 ⟨⟨48312081705, 48312081712⟩, ⟨47433669624, 49193920495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220856320 221184000 131399680 132792320 ⟨⟨47716892372, 47716892378⟩, ⟨46840680434, 48596522521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 221184000 221511680 131399680 132792320 ⟨⟨47611179521, 47611179527⟩, ⟨46736124115, 48489645636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 220856320 221184000 132792320 134184960 ⟨⟨48205174973, 48205174979⟩, ⟨47327923908, 49085845228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 221184000 221511680 132792320 134184960 ⟨⟨48098440710, 48098440716⟩, ⟨47222347798, 48977945318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 220528640 134184960 135577600 ⟨⟨48909204235, 48909204238⟩, ⟨48028586619, 49793257057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 220528640 220856320 134184960 135577600 ⟨⟨48801102116, 48801102122⟩, ⟨47921650003, 49683981900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 220528640 135577600 136970240 ⟨⟨49398960981, 49398960983⟩, ⟨48517302443, 50284055675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 220528640 220856320 135577600 136970240 ⟨⟨49289838374, 49289838379⟩, ⟨48409346951, 50173758429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 220856320 221184000 134184960 135577600 ⟨⟨48693174430, 48693174435⟩, ⟨47814884948, 49574884072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 221184000 221511680 134184960 135577600 ⟨⟨48585420490, 48585420497⟩, ⟨47708290775, 49465962882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 220856320 221184000 135577600 136970240 ⟨⟨49180891473, 49180891478⟩, ⟨48301564288, 50063639788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 221184000 221511680 135577600 136970240 ⟨⟨49072119588, 49072119593⟩, ⟨48193953774, 49953699055⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 221511680 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 220856320) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 220528640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 220528640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 221184000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 221184000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 220856320) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 220528640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 220528640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 221184000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 221184000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (169/640 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((221511680 : ℤ) : ℝ) / (D : ℝ)) = (169/640 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
