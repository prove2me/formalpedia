-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_224133120_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:43:09.414992+00:00
-- url     : https://prove2.me/submissions/6c01bf9e-b4eb-4055-bf67-551596a22b9c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 171/640]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 222822400 223150080 125829120 127221760 ⟨⟨45153723762, 45153723768⟩, ⟨44288532963, 46022283982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 223150080 223477760 125829120 127221760 ⟨⟨45053096034, 45053096041⟩, ⟨44189038338, 45920515773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 223150080 127221760 128614400 ⟨⟨45636995520, 45636995525⟩, ⟨44770772601, 46506588908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223150080 223477760 127221760 128614400 ⟨⟨45535347232, 45535347237⟩, ⟨44670259055, 46403798509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 223477760 223805440 125829120 127221760 ⟨⟨44952629730, 44952629732⟩, ⟨44089702366, 45818911779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 223805440 224133120 125829120 127221760 ⟨⟨44852324209, 44852324214⟩, ⟨43990524417, 45717471362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 223477760 223805440 127221760 128614400 ⟨⟨45433861659, 45433861662⟩, ⟨44569905452, 46301173619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 223805440 224133120 127221760 128614400 ⟨⟨45332538160, 45332538165⟩, ⟨44469711160, 46198713597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 223150080 128614400 130007040 ⟨⟨46119991605, 46119991611⟩, ⟨45252737243, 46990617485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 223150080 223477760 128614400 130007040 ⟨⟨46017324460, 46017324467⟩, ⟨45151206472, 46886806604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222822400 223150080 130007040 131399680 ⟨⟨46602712723, 46602712730⟩, ⟨45734427590, 47474370415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 223150080 223477760 130007040 131399680 ⟨⟨46499028421, 46499028426⟩, ⟨45631881285, 47369540761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 223477760 223805440 128614400 130007040 ⟨⟨45914821316, 45914821319⟩, ⟨45049836927, 46783162522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 223805440 224133120 128614400 130007040 ⟨⟨45812481525, 45812481530⟩, ⟨44948627970, 46679684588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 223477760 223805440 130007040 131399680 ⟨⟨46395509394, 46395509397⟩, ⟨45529497480, 47264879181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 223805440 224133120 130007040 131399680 ⟨⟨46292154991, 46292154997⟩, ⟨45427275532, 47160385025⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 224133120 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 223477760) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 223150080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 223150080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 223805440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 223805440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 223477760) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 223150080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 223150080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 223805440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 223805440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (171/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((224133120 : ℤ) : ℝ) / (D : ℝ)) = (171/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
