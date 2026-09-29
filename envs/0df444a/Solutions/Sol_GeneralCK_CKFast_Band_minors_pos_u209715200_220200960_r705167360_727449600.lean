-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r705167360_727449600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:03:46.97837+00:00
-- url     : https://prove2.me/submissions/7a12e787-24e2-4918-8c96-081b79a50804

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [269/320, 111/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 705167360 710737920 ⟨⟨245568770860, 245568770870⟩, ⟨236584129735, 254716500948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 212336640 710737920 716308480 ⟨⟨247317225649, 247317225659⟩, ⟨238305998039, 256491336866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 214958080 705167360 710737920 ⟨⟨242072941534, 242072941543⟩, ⟨233155224604, 251153421634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 710737920 716308480 ⟨⟨243801433598, 243801433608⟩, ⟨234857089516, 252908362372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 212336640 716308480 721879040 ⟨⟨249064180722, 249064180731⟩, ⟨240026384605, 258264650008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 212336640 721879040 727449600 ⟨⟨250809661067, 250809661077⟩, ⟨241745313960, 260036465802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 214958080 716308480 721879040 ⟨⟨245528479616, 245528479625⟩, ⟨236557524632, 254661835825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212336640 214958080 721879040 727449600 ⟨⟨247254103564, 247254103573⟩, ⟨238256553490, 256413866387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 705167360 710737920 ⟨⟨238594562688, 238594562692⟩, ⟨229743231927, 247608316441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 217579520 710737920 716308480 ⟨⟨240302991573, 240302991577⟩, ⟨231425003274, 249343250591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 705167360 710737920 ⟨⟨235133265443, 235133265453⟩, ⟨226347791527, 244080808373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 220200960 710737920 716308480 ⟨⟨236821533697, 236821533707⟩, ⟨228009381885, 245795627796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214958080 217579520 716308480 721879040 ⟨⟨242010026920, 242010026925⟩, ⟨233105395622, 251076771776⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214958080 217579520 721879040 727449600 ⟨⟨243715691727, 243715691732⟩, ⟨234784431556, 252808903384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 220200960 716308480 721879040 ⟨⟨238508459766, 238508459775⟩, ⟨229669642905, 247509087398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217579520 220200960 721879040 727449600 ⟨⟨240194065693, 240194065702⟩, ⟨231328596240, 249221209592⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 705167360 727449600 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 716308480) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 710737920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 710737920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212336640) (by decide) (join_sr (m := 721879040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 721879040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 716308480) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 710737920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 710737920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 217579520) (by decide) (join_sr (m := 721879040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 721879040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (269/320 : ℝ) (111/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  have e3 : (((727449600 : ℤ) : ℝ) / (D : ℝ)) = (111/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
