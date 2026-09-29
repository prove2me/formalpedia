-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u196608000_199229440_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:41:25.78065+00:00
-- url     : https://prove2.me/submissions/fff2473a-c3c3-4ebf-9504-33a9cb09e5f5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [15/64, 19/80]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 196608000 197263360 159252480 162037760 ⟨⟨67545211569, 67545211576⟩, ⟨65562340892, 69544290639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 197263360 197918720 159252480 162037760 ⟨⟨67259568782, 67259568789⟩, ⟨65282412973, 69252856927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 196608000 197263360 162037760 164823040 ⟨⟨68661660459, 68661660465⟩, ⟨66674253665, 70665274769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 197263360 197918720 162037760 164823040 ⟨⟨68371713202, 68371713208⟩, ⟨66390033328, 70369524815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 197918720 198574080 159252480 162037760 ⟨⟨66974964444, 66974964448⟩, ⟨65003492560, 68962493176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 198574080 199229440 159252480 162037760 ⟨⟨66691390142, 66691390150⟩, ⟨64725571510, 68673190707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 197918720 198574080 162037760 164823040 ⟨⟨68082815339, 68082815341⟩, ⟨66106831443, 70074855759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 198574080 199229440 162037760 164823040 ⟨⟨67794958390, 67794958395⟩, ⟨65824639801, 69781258858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197263360 164823040 167608320 ⟨⟨69776461041, 69776461047⟩, ⟨67784528790, 71784599820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 197263360 197918720 164823040 167608320 ⟨⟨69482228020, 69482228026⟩, ⟨67496034562, 71484552507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 197263360 167608320 170393600 ⟨⟨70889623058, 70889623066⟩, ⟨68893175931, 72902275605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197263360 197918720 167608320 170393600 ⟨⟨70591122828, 70591122835⟩, ⟨68600426190, 72597949670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 197918720 198574080 164823040 167608320 ⟨⟨69189055145, 69189055149⟩, ⟨67208569543, 71185596841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 198574080 199229440 164823040 167608320 ⟨⟨68896933878, 68896933884⟩, ⟨66922125462, 70887724014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 198574080 167608320 170393600 ⟨⟨70293693314, 70293693318⟩, ⟨68308716234, 72294725940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 198574080 199229440 167608320 170393600 ⟨⟨69997325915, 69997325922⟩, ⟨68018037730, 71992595547⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 196608000 199229440 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 197263360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 198574080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 197918720) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 197263360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 197263360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 198574080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 198574080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (15/64 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
