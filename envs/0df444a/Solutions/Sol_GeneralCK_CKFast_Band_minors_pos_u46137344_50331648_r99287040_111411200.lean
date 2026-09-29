-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u46137344_50331648_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:43:45.936835+00:00
-- url     : https://prove2.me/submissions/b04acf2e-e5ef-4703-893e-57cd9996bd08

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/200, 3/50]`, `ρ ∈ [303/2560, 17/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 46137344 47185920 99287040 102318080 ⟨⟨143746207811, 143746207827⟩, ⟨135861332449, 151853935254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 46137344 47185920 102318080 105349120 ⟨⟨147097059374, 147097059387⟩, ⟨139211919387, 155202058824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 47185920 48234496 99287040 102318080 ⟨⟨141908350704, 141908350720⟩, ⟨134141546466, 149892294502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 47185920 48234496 102318080 105349120 ⟨⟨145234067242, 145234067255⟩, ⟨137466141632, 153216285137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 46137344 47185920 105349120 108380160 ⟨⟨150409020655, 150409020668⟩, ⟨142524210230, 158510747391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 46137344 47185920 108380160 111411200 ⟨⟨153683100811, 153683100824⟩, ⟨145799181122, 161781042322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 47185920 48234496 105349120 108380160 ⟨⟨148521828309, 148521828323⟩, ⟨140753368150, 156501779090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 47185920 48234496 108380160 111411200 ⟨⟨151772603978, 151772603991⟩, ⟨144004164385, 159749777441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 48234496 49283072 99287040 102318080 ⟨⟨140116280579, 140116280592⟩, ⟨132463841762, 147980376154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 48234496 49283072 102318080 105349120 ⟨⟨143416992119, 143416992131⟩, ⟨135762634319, 151280296166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 49283072 50331648 99287040 102318080 ⟨⟨138368163641, 138368163657⟩, ⟨130826556752, 146116161854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 49283072 50331648 102318080 105349120 ⟨⟨141644012160, 141644012172⟩, ⟨134099743580, 149392090346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 48234496 49283072 105349120 108380160 ⟨⟨146680656781, 146680656797⟩, ⟨139024958876, 154542632502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 48234496 49283072 108380160 111411200 ⟨⟨149908207312, 149908207325⟩, ⟨142251717739, 157768347733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 49283072 50331648 105349120 108380160 ⟨⟨144883696924, 144883696939⟩, ⟨137337337109, 152631323463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 49283072 50331648 108380160 111411200 ⟨⟨148088115022, 148088115035⟩, ⟨140540205215, 155834786977⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 46137344 50331648 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 48234496) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 47185920) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 102318080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 47185920) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 108380160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 105349120) (by decide) (join_su (m := 49283072) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 102318080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 49283072) (by decide) (join_sr (m := 108380160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 108380160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/200 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((46137344 : ℤ) : ℝ) / (D : ℝ)) = (11/200 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
