-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_117964800_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:19:17.266231+00:00
-- url     : https://prove2.me/submissions/24738c86-a037-461f-94cf-54780c6766f3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 9/64]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 115998720 107479040 110428160 ⟨⟨81153242326, 81153242334⟩, ⟨78126232013, 84217452324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115998720 116654080 107479040 110428160 ⟨⟨80757667089, 80757667090⟩, ⟨77744446919, 83807787157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 115343360 115998720 110428160 113377280 ⟨⟨83155459574, 83155459582⟩, ⟨80121189600, 86226797050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 115998720 116654080 110428160 113377280 ⟨⟨82751672843, 82751672848⟩, ⟨79731204127, 85808912067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 116654080 117309440 107479040 110428160 ⟨⟨80364961370, 80364961377⟩, ⟨77365402697, 83401123984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 117309440 117964800 107479040 110428160 ⟨⟨79975088682, 79975088689⟩, ⟨76989064700, 82997424389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 116654080 117309440 110428160 113377280 ⟨⟨82350796809, 82350796816⟩, ⟨79344001060, 85394069832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 117309440 117964800 110428160 113377280 ⟨⟨81952794644, 81952794651⟩, ⟨78959545404, 84982231617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 115998720 113377280 116326400 ⟨⟨85148974922, 85148974931⟩, ⟨82107539823, 88227345356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 115998720 116654080 113377280 116326400 ⟨⟨84737079431, 84737079437⟩, ⟨81709455346, 87801344626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 115343360 115998720 116326400 119275520 ⟨⟨87133888925, 87133888935⟩, ⟨84085381528, 90219199507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 115998720 116654080 116326400 119275520 ⟨⟨86713985646, 86713985651⟩, ⟨83679297706, 89785185307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 116654080 117309440 113377280 116326400 ⟨⟨84328134487, 84328134494⟩, ⟨81314193505, 87378426063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 117309440 117964800 113377280 116326400 ⟨⟨83922102949, 83922102957⟩, ⟨80921718978, 86958550632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 116654080 117309440 116326400 119275520 ⟨⟨86297071474, 86297071484⟩, ⟨83276075477, 89354291382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 117309440 117964800 116326400 119275520 ⟨⟨85883108979, 85883108989⟩, ⟨82875679216, 88926478420⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 117964800 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 116654080) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 115998720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 115998720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 117309440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 117309440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 116654080) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 115998720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 115998720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 117309440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 117309440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (9/64 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((117964800 : ℤ) : ℝ) / (D : ℝ)) = (9/64 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
