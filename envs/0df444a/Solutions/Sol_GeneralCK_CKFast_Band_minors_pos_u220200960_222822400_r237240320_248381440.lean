-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_222822400_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:29:41.910974+00:00
-- url     : https://prove2.me/submissions/5dc4fef5-3a3e-4b96-ba20-f479a27485ac

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 17/64]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 220856320 237240320 240025600 ⟨⟨84572262051, 84572262059⟩, ⟨82664377526, 86494102223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220856320 221511680 237240320 240025600 ⟨⟨84213312599, 84213312602⟩, ⟨82310466938, 86130059987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 220856320 240025600 242810880 ⟨⟨85511961663, 85511961670⟩, ⟨83600112182, 87437771468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 220856320 221511680 240025600 242810880 ⟨⟨85149396094, 85149396097⟩, ⟨83242594330, 87070104443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 221511680 222167040 237240320 240025600 ⟨⟨83855345733, 83855345739⟩, ⟨81957516054, 85767023555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222167040 222822400 237240320 240025600 ⟨⟨83498354417, 83498354423⟩, ⟨81605517999, 85404985718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222167040 240025600 242810880 ⟨⟨84787818675, 84787818680⟩, ⟨82886041767, 86703448765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222167040 222822400 240025600 242810880 ⟨⟨84427222344, 84427222352⟩, ⟨82530447593, 86337797196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 220856320 242810880 245596160 ⟨⟨86450727199, 86450727206⟩, ⟨84534917358, 88380501963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 220856320 221511680 242810880 245596160 ⟨⟨86084556294, 86084556297⟩, ⟨84173802930, 88009221025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 220856320 245596160 248381440 ⟨⟨87388563553, 87388563559⟩, ⟨85468797921, 89322298629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 220856320 221511680 245596160 248381440 ⟨⟨87018798023, 87018798025⟩, ⟨85104097536, 88947414583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 221511680 222167040 242810880 245596160 ⟨⟨85719379002, 85719379008⟩, ⟨83813659275, 87638956874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222167040 222822400 242810880 245596160 ⟨⟨85355188238, 85355188246⟩, ⟨83454479468, 87269702249⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 221511680 222167040 245596160 248381440 ⟨⟨86650031468, 86650031474⟩, ⟨84740373306, 88573552662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 222167040 222822400 245596160 248381440 ⟨⟨86282256784, 86282256790⟩, ⟨84377618287, 88200705583⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 222822400 237240320 248381440 t = true :=
  ⟨_, (join_sr (m := 242810880) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 240025600) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 220856320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 240025600) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 222167040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 221511680) (by decide) (join_sr (m := 245596160) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 220856320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 245596160) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 222167040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
