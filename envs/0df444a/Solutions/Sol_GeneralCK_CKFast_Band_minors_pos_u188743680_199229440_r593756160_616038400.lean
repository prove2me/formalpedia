-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r593756160_616038400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:01:20.912062+00:00
-- url     : https://prove2.me/submissions/c09394e2-05c7-47a6-85ef-e606d06e153f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [453/640, 47/64]` by 12 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 593756160 604897280 ⟨⟨236635035252, 236635035258⟩, ⟨226050110526, 247461453507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 191365120 193986560 593756160 604897280 ⟨⟨233371038038, 233371038048⟩, ⟨222886731813, 244095235147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 191365120 604897280 616038400 ⟨⟨240531859450, 240531859457⟩, ⟨229890869665, 251413061132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 604897280 616038400 ⟨⟨237226877841, 237226877851⟩, ⟨226686274129, 248006185525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 196608000 593756160 599326720 ⟨⟨229174736403, 229174736412⟩, ⟨220305961924, 238214711606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193986560 196608000 599326720 604897280 ⟨⟨231084586518, 231084586528⟩, ⟨222188991990, 240151107234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 196608000 199229440 593756160 599326720 ⟨⟨225966496625, 225966496634⟩, ⟨217169809828, 234933547864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 196608000 199229440 599326720 604897280 ⟨⟨227855571890, 227855571899⟩, ⟨219031999157, 236849264479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 196608000 604897280 610467840 ⟨⟨232991909994, 232991910004⟩, ⟨224069537365, 242084929072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 193986560 196608000 610467840 616038400 ⟨⟨234896743218, 234896743228⟩, ⟨225947633722, 244016214212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 199229440 604897280 610467840 ⟨⟨229742207943, 229742207953⟩, ⟨220891788777, 238762497242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 196608000 199229440 610467840 616038400 ⟨⟨231626439683, 231626439692⟩, ⟨222749212906, 240673281715⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 593756160 616038400 t = true :=
  ⟨_, (join_su (m := 193986560) (by decide) (join_sr (m := 604897280) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 191365120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 604897280) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 599326720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 599326720) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 196608000) (by decide) (join_sr (m := 610467840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 610467840) (by decide) (leaf_ok cell10) (leaf_ok cell11)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (453/640 : ℝ) (47/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  have e3 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
