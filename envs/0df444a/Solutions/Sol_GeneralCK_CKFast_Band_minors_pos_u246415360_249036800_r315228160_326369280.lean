-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r315228160_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:47:39.139915+00:00
-- url     : https://prove2.me/submissions/61e9193d-54a8-4077-b65b-55d940e667d1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [481/1280, 249/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 315228160 318013440 ⟨⟨93084035792, 93084035798⟩, ⟨91261132248, 94919238075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247070720 247726080 315228160 318013440 ⟨⟨92666506874, 92666506876⟩, ⟨90848081858, 94497191040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247726080 318013440 320798720 ⟨⟨93657624808, 93657624815⟩, ⟨90504946155, 96845863593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 248381440 315228160 318013440 ⟨⟨92249821474, 92249821480⟩, ⟨90435858067, 94076004643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 248381440 249036800 315228160 318013440 ⟨⟨91833973979, 91833973985⟩, ⟨90024455361, 93655673161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247726080 248381440 318013440 320798720 ⟨⟨93027450874, 93027450881⟩, ⟨91209943169, 94857187421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 248381440 249036800 318013440 320798720 ⟨⟨92608386934, 92608386941⟩, ⟨90795331804, 94433631823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 246415360 247726080 320798720 323584000 ⟨⟨94439584896, 94439584902⟩, ⟨91280249442, 97634519921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247726080 323584000 326369280 ⟨⟨95221048220, 95221048226⟩, ⟨92055057212, 98422678085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 248381440 320798720 323584000 ⟨⟨93804590391, 93804590397⟩, ⟨91983539605, 95637879049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 248381440 249036800 320798720 323584000 ⟨⟨93382316132, 93382316139⟩, ⟨91565725657, 95211105513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247726080 249036800 323584000 326369280 ⟨⟨94368397741, 94368397748⟩, ⟨91215218322, 97557033709⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 315228160 326369280 t = true :=
  ⟨_, (join_sr (m := 320798720) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 318013440) (by decide) (join_su (m := 247070720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 318013440) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 248381440) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 247726080) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 323584000) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (481/1280 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
