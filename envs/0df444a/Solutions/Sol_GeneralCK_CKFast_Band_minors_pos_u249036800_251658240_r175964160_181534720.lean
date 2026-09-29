-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r175964160_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:11:03.191647+00:00
-- url     : https://prove2.me/submissions/e9a357d3-ba18-4c2b-80b1-02377776b9a3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [537/2560, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 175964160 177356800 ⟨⟨51997313839, 51997313845⟩, ⟨50598163637, 53404708239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249036800 249692160 177356800 178749440 ⟨⟨52396556572, 52396556577⟩, ⟨50995735097, 53805628191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249692160 250347520 175964160 177356800 ⟨⟨51753033463, 51753033470⟩, ⟨50356654841, 53157630672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 177356800 178749440 ⟨⟨52150494705, 52150494710⟩, ⟨50752449205, 53556764760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 249692160 178749440 180142080 ⟨⟨52795648125, 52795648130⟩, ⟨51393155560, 54206396773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 249036800 249692160 180142080 181534720 ⟨⟨53194588840, 53194588845⟩, ⟨51790425367, 54607014327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250347520 178749440 180142080 ⟨⟨52547806763, 52547806770⟩, ⟨51148094558, 53955749486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249692160 250347520 180142080 181534720 ⟨⟨52944969976, 52944969981⟩, ⟨51543591234, 54354585187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 251002880 175964160 177356800 ⟨⟨51509352349, 51509352352⟩, ⟨50115732646, 52911165180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250347520 251002880 177356800 178749440 ⟨⟨51905035232, 51905035234⟩, ⟨50509753042, 53308516542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251002880 251658240 175964160 177356800 ⟨⟨51266266125, 51266266131⟩, ⟨49875392773, 52665307310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251002880 251658240 177356800 178749440 ⟨⟨51660173763, 51660173768⟩, ⟨50267642307, 53060879065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 178749440 180142080 ⟨⟨52300570907, 52300570910⟩, ⟨50903626388, 53705720530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251002880 180142080 181534720 ⟨⟨52695959707, 52695959709⟩, ⟨51297353018, 54102777475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251658240 178749440 180142080 ⟨⟨52053936149, 52053936154⟩, ⟨50659746736, 53456305412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 180142080 181534720 ⟨⟨52447553607, 52447553612⟩, ⟨51051706384, 53851586680⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 175964160 181534720 t = true :=
  ⟨_, (join_su (m := 250347520) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 177356800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 249692160) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 180142080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 178749440) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 177356800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 251002880) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 180142080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (537/2560 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
