-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r650117120_697303040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:54:46.171033+00:00
-- url     : https://prove2.me/submissions/c1dce280-be08-460e-9edd-e3e4b21cc47f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [31/40, 133/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 650117120 661913600 ⟨⟨347671478909, 347671478921⟩, ⟨333796557797, 361808029541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 128450560 131072000 650117120 661913600 ⟨⟨343493585165, 343493585178⟩, ⟨329752556868, 357496070078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 128450560 661913600 673710080 ⟨⟨352639568852, 352639568866⟩, ⟨338727024448, 366808618044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 661913600 673710080 ⟨⟨348429532360, 348429532372⟩, ⟨334649344909, 362466245202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131072000 133693440 650117120 661913600 ⟨⟨339354240472, 339354240483⟩, ⟨325745464446, 353224224602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 133693440 136314880 650117120 661913600 ⟨⟨335252459158, 335252459171⟩, ⟨321774331365, 348991475005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131072000 133693440 661913600 673710080 ⟨⟨344257468424, 344257468435⟩, ⟨330608069179, 358163333683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 133693440 136314880 661913600 673710080 ⟨⟨340122412104, 340122412115⟩, ⟨326602266553, 353898888428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 128450560 673710080 685506560 ⟨⟨357587955719, 357587955732⟩, ⟨343638132310, 371789164464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 128450560 131072000 673710080 685506560 ⟨⟨353346219502, 353346219515⟩, ⟨339527221613, 367416813523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 128450560 685506560 697303040 ⟨⟨362517420920, 362517420930⟩, ⟨348530642183, 376750469504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 128450560 131072000 685506560 697303040 ⟨⟨358244404658, 358244404668⟩, ⟨344386924831, 372348552122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131072000 133693440 673710080 685506560 ⟨⟨349141877804, 349141877815⟩, ⟨335452207084, 363083271328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133693440 136314880 673710080 685506560 ⟨⟨344973985960, 344973985972⟩, ⟨331412176131, 358787565304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 131072000 133693440 685506560 697303040 ⟨⟨354008203761, 354008203770⟩, ⟨340278593522, 367984791384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 136314880 685506560 697303040 ⟨⟨349807893397, 349807893407⟩, ⟨336204753422, 363658236651⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 650117120 697303040 t = true :=
  ⟨_, (join_sr (m := 673710080) (by decide) (join_su (m := 131072000) (by decide) (join_sr (m := 661913600) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 128450560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 661913600) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 133693440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 131072000) (by decide) (join_sr (m := 685506560) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 128450560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 685506560) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 133693440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (31/40 : ℝ) (133/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  have e3 : (((697303040 : ℤ) : ℝ) / (D : ℝ)) = (133/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
