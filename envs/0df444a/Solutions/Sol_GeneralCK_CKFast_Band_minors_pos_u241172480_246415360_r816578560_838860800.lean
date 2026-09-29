-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r816578560_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:22:40.698194+00:00
-- url     : https://prove2.me/submissions/245acd34-8c75-48cd-b628-81a667536cf0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [623/640, 1]` by 12 cells of the computing
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
theorem cell0 : cellOK 241172480 243793920 816578560 822149120 ⟨⟨234590283093, 234590283097⟩, ⟨225845607762, 243494070612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 243793920 822149120 827719680 ⟨⟨236077273657, 236077273660⟩, ⟨227306084297, 245007571404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 245104640 816578560 822149120 ⟨⟨231797547268, 231797547277⟩, ⟨226869145734, 236778043189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 245104640 246415360 816578560 822149120 ⟨⟨229939467397, 229939467402⟩, ⟨225032141911, 234898820021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 245104640 822149120 827719680 ⟨⟨233269309497, 233269309506⟩, ⟨228327050824, 238263640885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245104640 246415360 822149120 827719680 ⟨⟨231401049792, 231401049795⟩, ⟨226479879980, 236374228717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241172480 243793920 827719680 833290240 ⟨⟨237563616937, 237563616941⟩, ⟨228765907869, 246520426412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 241172480 243793920 833290240 838860800 ⟨⟨239049326673, 239049326678⟩, ⟨230225091982, 248032649580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 245104640 827719680 833290240 ⟨⟨234740444696, 234740444706⟩, ⟨229784327760, 239748611470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245104640 246415360 827719680 833290240 ⟨⟨232862018444, 232862018449⟩, ⟨227927002875, 237849023920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 245104640 833290240 838860800 ⟨⟨236210966140, 236210966150⟩, ⟨231240989683, 241232968348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245104640 246415360 833290240 838860800 ⟨⟨234322386331, 234322386336⟩, ⟨229373523439, 239323218730⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 816578560 838860800 t = true :=
  ⟨_, (join_sr (m := 827719680) (by decide) (join_su (m := 243793920) (by decide) (join_sr (m := 822149120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 822149120) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell2) (leaf_ok cell3)) (join_su (m := 245104640) (by decide) (leaf_ok cell4) (leaf_ok cell5)))) (join_su (m := 243793920) (by decide) (join_sr (m := 833290240) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 833290240) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 245104640) (by decide) (leaf_ok cell10) (leaf_ok cell11)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (623/640 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((816578560 : ℤ) : ℝ) / (D : ℝ)) = (623/640 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
