-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u186122240_188743680_r148111360_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:37:12.6572+00:00
-- url     : https://prove2.me/submissions/bfee9626-ca3f-4b32-92a4-0fc7ffe08c3f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [71/320, 9/40]`, `ρ ∈ [113/640, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 186122240 186777600 148111360 150896640 ⟨⟨67496477712, 67496477720⟩, ⟨65436783232, 69573703212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 186777600 187432960 148111360 150896640 ⟨⟨67211181742, 67211181749⟩, ⟨65157686357, 69282120630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 186122240 186777600 150896640 153681920 ⟨⟨68691365736, 68691365744⟩, ⟨66626886689, 70773370316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 186777600 187432960 150896640 153681920 ⟨⟨68401491221, 68401491227⟩, ⟨66343224082, 70477196733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 187432960 188088320 148111360 150896640 ⟨⟨66927020720, 66927020727⟩, ⟨64879688722, 68991709408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188088320 188743680 148111360 150896640 ⟨⟨66643985042, 66643985043⟩, ⟨64602781046, 68702459602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 187432960 188088320 150896640 153681920 ⟨⟨68112764601, 68112764607⟩, ⟨66060673666, 70182207446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 188088320 188743680 150896640 153681920 ⟨⟨67825176190, 67825176193⟩, ⟨65779226078, 69888392434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 186122240 186777600 153681920 156467200 ⟨⟨69884228474, 69884228481⟩, ⟨67814979134, 71970997727⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186777600 187432960 153681920 156467200 ⟨⟨69589798162, 69589798168⟩, ⟨67526773317, 71670256118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 186777600 156467200 159252480 ⟨⟨71075078698, 71075078705⟩, ⟨69001073227, 73166598330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186777600 187432960 156467200 159252480 ⟨⟨70776115145, 70776115151⟩, ⟨68708346531, 72861311477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 187432960 188088320 153681920 156467200 ⟨⟨69296528460, 69296528468⟩, ⟨67239692413, 71370711510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 188088320 188743680 153681920 156467200 ⟨⟨69004409606, 69004409609⟩, ⟨66953726979, 71072353801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188088320 156467200 159252480 ⟨⟨70478324688, 70478324694⟩, ⟨68416757244, 72557234094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 188088320 188743680 156467200 159252480 ⟨⟨70181697487, 70181697490⟩, ⟨68126295845, 72254356004⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 186122240 188743680 148111360 159252480 t = true :=
  ⟨_, (join_sr (m := 153681920) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 186777600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 186777600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 150896640) (by decide) (join_su (m := 188088320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 188088320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 187432960) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 186777600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 186777600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 156467200) (by decide) (join_su (m := 188088320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 188088320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (71/320 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
