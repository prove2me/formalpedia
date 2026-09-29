-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_83886080_r741867520_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T11:00:05.097304+00:00
-- url     : https://prove2.me/submissions/c092dec0-f7f8-4d3d-a8ff-01dc7828ba15

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 1/10]`, `ρ ∈ [283/320, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 71303168 741867520 766115840 ⟨⟨497202037103, 497202037118⟩, ⟨466842659668, 528015174738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 71303168 75497472 741867520 766115840 ⟨⟨488458783665, 488458783678⟩, ⟨458554597731, 518843644641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 71303168 766115840 790364160 ⟨⟨508029592154, 508029592168⟩, ⟨477737525113, 538714358425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 71303168 75497472 766115840 790364160 ⟨⟨499251935673, 499251935687⟩, ⟨469395966972, 529529684420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 79691776 741867520 766115840 ⟨⟨479880186388, 479880186401⟩, ⟨450421701307, 509843832917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 79691776 83886080 741867520 766115840 ⟨⟨471456788964, 471456788980⟩, ⟨442435135850, 501005880365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 75497472 79691776 766115840 790364160 ⟨⟨490632747937, 490632747950⟩, ⟨461204433282, 520509486473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 79691776 83886080 766115840 790364160 ⟨⟨482162930753, 482162930767⟩, ⟨453154394232, 511644311183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 67108864 71303168 790364160 814612480 ⟨⟨518784428347, 518784428360⟩, ⟨488556140924, 549345686497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 71303168 75497472 790364160 814612480 ⟨⟨509972858899, 509972858913⟩, ⟨480162246864, 540147543632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 67108864 71303168 814612480 838860800 ⟨⟨529475221711, 529475221725⟩, ⟨499307136017, 559917693737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 71303168 75497472 814612480 838860800 ⟨⟨520630024788, 520630024802⟩, ⟨490861821592, 550705610000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 75497472 79691776 790364160 814612480 ⟨⟨501313761771, 501313761784⟩, ⟨471913358630, 531106901880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 79691776 83886080 790364160 814612480 ⟨⟨492798374809, 492798374823⟩, ⟨463801234436, 522214686190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 75497472 79691776 814612480 838860800 ⟨⟨511931484034, 511931484047⟩, ⟨482556612374, 541644301436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 79691776 83886080 814612480 838860800 ⟨⟨503371153441, 503371153455⟩, ⟨474383539396, 532725046822⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 83886080 741867520 838860800 t = true :=
  ⟨_, (join_sr (m := 790364160) (by decide) (join_su (m := 75497472) (by decide) (join_sr (m := 766115840) (by decide) (join_su (m := 71303168) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 71303168) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 766115840) (by decide) (join_su (m := 79691776) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 79691776) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 75497472) (by decide) (join_sr (m := 814612480) (by decide) (join_su (m := 71303168) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 71303168) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 814612480) (by decide) (join_su (m := 79691776) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 79691776) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (283/320 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((741867520 : ℤ) : ℝ) / (D : ℝ)) = (283/320 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
