-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r697303040_744488960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:14:10.325526+00:00
-- url     : https://prove2.me/submissions/24b2ff83-af57-4113-bc1d-b806e6727762

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [133/160, 71/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 697303040 709099520 ⟨⟨333963583887, 333963583899⟩, ⟨320925742808, 347244887814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149422080 152043520 697303040 709099520 ⟨⟨329925904245, 329925904251⟩, ⟨317005674638, 343089551008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 149422080 709099520 720896000 ⟨⟨338598185599, 338598185610⟩, ⟨325513606938, 351922465920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 709099520 720896000 ⟨⟨334525850109, 334525850114⟩, ⟨321557848163, 347733661480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152043520 154664960 697303040 709099520 ⟨⟨325918028376, 325918028388⟩, ⟨313114245388, 338965119399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154664960 157286400 697303040 709099520 ⟨⟨321939265682, 321939265695⟩, ⟨309250785356, 334870884294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 152043520 154664960 709099520 720896000 ⟨⟨330482871596, 330482871608⟩, ⟨317630334298, 343575259336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 154664960 157286400 709099520 720896000 ⟨⟨326468573544, 326468573555⟩, ⟨313730408248, 339446566380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 149422080 720896000 732692480 ⟨⟨343218916848, 343218916860⟩, ⟨330087881856, 356585874344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 149422080 152043520 720896000 732692480 ⟨⟨339112269771, 339112269777⟩, ⟨326096774372, 352363947390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 149422080 732692480 744488960 ⟨⟨347826337577, 347826337588⟩, ⟨334649112559, 361235687229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 149422080 152043520 732692480 744488960 ⟨⟨343685705773, 343685705779⟩, ⟨330622981267, 356980965128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152043520 154664960 720896000 732692480 ⟨⟨335034530165, 335034530176⟩, ⟨322133514355, 348171917977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154664960 157286400 720896000 732692480 ⟨⟨330985035348, 330985035361⟩, ⟨318197457132, 344009108280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 152043520 154664960 732692480 744488960 ⟨⟨339573529570, 339573529581⟩, ⟨326624296920, 352755634298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 154664960 157286400 732692480 744488960 ⟨⟨335489159885, 335489159896⟩, ⟨322652427080, 348559031895⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 697303040 744488960 t = true :=
  ⟨_, (join_sr (m := 720896000) (by decide) (join_su (m := 152043520) (by decide) (join_sr (m := 709099520) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 149422080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 709099520) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 154664960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 152043520) (by decide) (join_sr (m := 732692480) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 149422080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 732692480) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 154664960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (133/160 : ℝ) (71/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((697303040 : ℤ) : ℝ) / (D : ℝ)) = (133/160 : ℝ) := by norm_num [D]
  have e3 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
