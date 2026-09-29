-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_234618880_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:19:00.432725+00:00
-- url     : https://prove2.me/submissions/16f7230d-ed51-4d76-8688-97434ca4e685

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 179/640]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 233308160 233635840 125829120 127221760 ⟨⟨42010658334, 42010658337⟩, ⟨41180405214, 42844057133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233635840 233963520 125829120 127221760 ⟨⟨41914895497, 41914895504⟩, ⟨41085692021, 42747238056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233635840 127221760 128614400 ⟨⟨42461892894, 42461892896⟩, ⟨41630659046, 43296273711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233635840 233963520 127221760 128614400 ⟨⟨42365148824, 42365148830⟩, ⟨41534966190, 43198471836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233963520 234291200 125829120 127221760 ⟨⟨41819275161, 41819275166⟩, ⟨40991118886, 42650563940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234291200 234618880 125829120 127221760 ⟨⟨41723796774, 41723796779⟩, ⟨40896685265, 42554034231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233963520 234291200 127221760 128614400 ⟨⟨42268548416, 42268548421⟩, ⟨41439414552, 43100816087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234291200 234618880 127221760 128614400 ⟨⟨42172091116, 42172091123⟩, ⟨41344003585, 43003305907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233635840 128614400 130007040 ⟨⟨42912902068, 42912902071⟩, ⟨42080687952, 43748264439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233635840 233963520 128614400 130007040 ⟨⟨42815178202, 42815178207⟩, ⟨41984016864, 43649481211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233635840 130007040 131399680 ⟨⟨43363686399, 43363686401⟩, ⟨42530492473, 44200029864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233635840 233963520 130007040 131399680 ⟨⟨43264984170, 43264984175⟩, ⟨42432844582, 44100266719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 233963520 234291200 128614400 130007040 ⟨⟨42717599152, 42717599159⟩, ⟨41887488148, 43550845265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234291200 234618880 128614400 130007040 ⟨⟨42620164363, 42620164368⟩, ⟨41791101250, 43452356041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233963520 234291200 130007040 131399680 ⟨⟨43166427904, 43166427911⟩, ⟨42335340205, 44000652008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234291200 234618880 130007040 131399680 ⟨⟨43068017042, 43068017048⟩, ⟨42237978789, 43901185163⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 234618880 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 233963520) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233635840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234291200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233963520) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 233635840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 234291200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (179/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
