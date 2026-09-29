-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r697303040_744488960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:54:50.469163+00:00
-- url     : https://prove2.me/submissions/66b90c96-bee4-4ac0-9f2c-4b3398a60039

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [133/160, 71/80]` by 11 cells of the computing
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
theorem cell0 : cellOK 125829120 131072000 697303040 709099520 ⟨⟨365272190244, 365272190256⟩, ⟨342346354474, 388862243750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 125829120 131072000 709099520 720896000 ⟨⟨370150902356, 370150902369⟩, ⟨347145221398, 393808131494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131072000 133693440 697303040 709099520 ⟨⟨358857164450, 358857164462⟩, ⟨345087927579, 372868629957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 133693440 136314880 697303040 709099520 ⟨⟨354624830916, 354624830928⟩, ⟨340980676272, 368511616609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131072000 133693440 709099520 720896000 ⟨⟨363689461785, 363689461797⟩, ⟨349880892781, 377735506193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 133693440 136314880 709099520 720896000 ⟨⟨359425479557, 359425479569⟩, ⟨345740607712, 373348403169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 125829120 131072000 720896000 732692480 ⟨⟨375013105277, 375013105288⟩, ⟨351928065589, 398736975203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 125829120 131072000 732692480 744488960 ⟨⟨379859500270, 379859500282⟩, ⟨356695559543, 403649501859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 133693440 720896000 732692480 ⟨⟨368505782141, 368505782152⟩, ⟨354658157772, 382586123036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 133693440 136314880 720896000 732692480 ⟨⟨364210505561, 364210505575⟩, ⟨350485196598, 378169278887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 131072000 136314880 732692480 744488960 ⟨⟨371139525291, 371139525303⟩, ⟨348330456305, 394581838209⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 697303040 744488960 t = true :=
  ⟨_, (join_sr (m := 720896000) (by decide) (join_su (m := 131072000) (by decide) (join_sr (m := 709099520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 709099520) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell2) (leaf_ok cell3)) (join_su (m := 133693440) (by decide) (leaf_ok cell4) (leaf_ok cell5)))) (join_su (m := 131072000) (by decide) (join_sr (m := 732692480) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 732692480) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (133/160 : ℝ) (71/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((697303040 : ℤ) : ℝ) / (D : ℝ)) = (133/160 : ℝ) := by norm_num [D]
  have e3 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
