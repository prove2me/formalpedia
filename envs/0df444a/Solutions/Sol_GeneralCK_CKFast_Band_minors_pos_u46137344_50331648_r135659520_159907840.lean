-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u46137344_50331648_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:48:25.360184+00:00
-- url     : https://prove2.me/submissions/fdb0e54d-7d45-4e8b-bd48-2b0bb332fd05

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/200, 3/50]`, `ρ ∈ [207/1280, 61/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 46137344 47185920 135659520 141721600 ⟨⟨183070416671, 183070416688⟩, ⟨172388640410, 194098006109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 47185920 48234496 135659520 141721600 ⟨⟨180976779862, 180976779876⟩, ⟨170444063030, 191847515004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 46137344 47185920 141721600 147783680 ⟨⟨188900011417, 188900011434⟩, ⟨178239992558, 199896380501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 47185920 48234496 141721600 147783680 ⟨⟨186775270473, 186775270489⟩, ⟨176261806451, 197617686035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 48234496 49283072 135659520 141721600 ⟨⟨178929050989, 178929051005⟩, ⟨168541263302, 189647330345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 49283072 50331648 135659520 141721600 ⟨⟨176925581372, 176925581388⟩, ⟨166678763193, 187495620523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 48234496 49283072 141721600 147783680 ⟨⟨184696233888, 184696233905⟩, ⟨174325333894, 195388934921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 49283072 50331648 141721600 147783680 ⟨⟨182661286224, 182661286240⟩, ⟨172429121654, 193208338445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 46137344 47185920 147783680 153845760 ⟨⟨194618171074, 194618171087⟩, ⟨183981358242, 205582196165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 47185920 48234496 147783680 153845760 ⟨⟨192464485361, 192464485374⟩, ⟨181971745031, 203277414393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 46137344 47185920 153845760 159907840 ⟨⟨200229900499, 200229900515⟩, ⟨189617569446, 211160617285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 47185920 48234496 153845760 159907840 ⟨⟨198049269373, 198049269389⟩, ⟨187578554980, 208831701271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 48234496 49283072 147783680 153845760 ⟨⟨190356259949, 190356259965⟩, ⟨180003736107, 201022178554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 49283072 50331648 147783680 153845760 ⟨⟨188291912792, 188291912808⟩, ⟨178075903657, 198814742402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 48234496 49283072 153845760 159907840 ⟨⟨195913819574, 195913819591⟩, ⟨185580995985, 206551904850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 49283072 50331648 153845760 159907840 ⟨⟨193822002410, 193822002423⟩, ⟨183623490453, 204319523683⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 46137344 50331648 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 48234496) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 47185920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 47185920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 49283072) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 49283072) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 48234496) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 47185920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 47185920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 153845760) (by decide) (join_su (m := 49283072) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 49283072) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/200 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((46137344 : ℤ) : ℝ) / (D : ℝ)) = (11/200 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
