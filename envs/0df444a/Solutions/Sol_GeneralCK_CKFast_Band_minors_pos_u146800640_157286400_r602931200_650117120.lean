-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r602931200_650117120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:12:10.294319+00:00
-- url     : https://prove2.me/submissions/6ee82715-f5d1-4fcf-82ff-5a7fe391192e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [23/32, 31/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 602931200 614727680 ⟨⟨296316375598, 296316375609⟩, ⟨283664513693, 309241222755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149422080 152043520 602931200 614727680 ⟨⟨292570621298, 292570621303⟩, ⟨280044505871, 305368387865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 149422080 614727680 626524160 ⟨⟨301083526079, 301083526090⟩, ⟨288382079254, 314054317404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 614727680 626524160 ⟨⟨297299662443, 297299662449⟩, ⟨284722964284, 310144538448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152043520 154664960 602931200 614727680 ⟨⟨288858097405, 288858097418⟩, ⟨276456114818, 301530365759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154664960 157286400 602931200 614727680 ⟨⟨285177992038, 285177992049⟩, ⟨272898563564, 297726311911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 152043520 154664960 614727680 626524160 ⟨⟨293548619737, 293548619747⟩, ⟨281095115294, 306269099488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 154664960 157286400 614727680 626524160 ⟨⟨289829602047, 289829602058⟩, ⟨277497769302, 302427174053⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 149422080 626524160 638320640 ⟨⟨305831887370, 305831887381⟩, ⟨293081274794, 318848190629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 149422080 152043520 626524160 638320640 ⟨⟨302010420429, 302010420433⟩, ⟨289383552034, 314901978374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 149422080 638320640 650117120 ⟨⟨310562122038, 310562122049⟩, ⟨297762743595, 323623523778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 149422080 152043520 638320640 650117120 ⟨⟨306703535099, 306703535104⟩, ⟨294026890339, 319641365660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152043520 154664960 626524160 638320640 ⟨⟨298221358480, 298221358490⟩, ⟨285716737268, 310989627791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154664960 157286400 626524160 638320640 ⟨⟨294463921364, 294463921374⟩, ⟨282080081351, 307110330167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 152043520 154664960 638320640 650117120 ⟨⟨302876931335, 302876931346⟩, ⟨290321580471, 315692585930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 154664960 157286400 638320640 650117120 ⟨⟨299081546113, 299081546123⟩, ⟨286646078520, 311776393322⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 602931200 650117120 t = true :=
  ⟨_, (join_sr (m := 626524160) (by decide) (join_su (m := 152043520) (by decide) (join_sr (m := 614727680) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 149422080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 614727680) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 154664960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 152043520) (by decide) (join_sr (m := 638320640) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 149422080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 638320640) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 154664960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (23/32 : ℝ) (31/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  have e3 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
