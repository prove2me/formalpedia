-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_157286400_r190054400_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:48:34.317912+00:00
-- url     : https://prove2.me/submissions/0ea83208-5572-45e9-9a63-829b35318c69

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 3/16]`, `ρ ∈ [29/128, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 152043520 153354240 190054400 193003520 ⟨⟨105509335176, 105509335183⟩, ⟨101381072736, 109698533548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 152043520 153354240 193003520 195952640 ⟨⟨106990659237, 106990659244⟩, ⟨102852760844, 111189421501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 153354240 154664960 190054400 193003520 ⟨⟨104637767617, 104637767621⟩, ⟨100535352855, 108800508909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 153354240 154664960 193003520 195952640 ⟨⟨106108894044, 106108894048⟩, ⟨101996864954, 110281181716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152043520 153354240 195952640 198901760 ⟨⟨108468415042, 108468415049⟩, ⟨104320926194, 112676695104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 152043520 153354240 198901760 201850880 ⟨⟨109942631605, 109942631613⟩, ⟨105785597322, 114160383857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 153354240 154664960 195952640 198901760 ⟨⟨107576525755, 107576525757⟩, ⟨103454926655, 111758314889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 153354240 154664960 198901760 201850880 ⟨⟨109040690921, 109040690925⟩, ⟨104909565671, 113231937075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 154664960 155975680 190054400 193003520 ⟨⟨103774285659, 103774285667⟩, ⟨99697368458, 107910930559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 154664960 155975680 193003520 195952640 ⟨⟨105235266103, 105235266110⟩, ⟨101148757136, 109381438801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 155975680 157286400 190054400 193003520 ⟨⟨102918742085, 102918742093⟩, ⟨98866979437, 107029643913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 155975680 157286400 193003520 195952640 ⟨⟨104369627797, 104369627805⟩, ⟨100308296842, 108490037824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154664960 155975680 195952640 198901760 ⟨⟨106692823943, 106692823950⟩, ⟨102596766376, 110848480682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154664960 155975680 198901760 201850880 ⟨⟨108146986538, 108146986547⟩, ⟨104041423093, 112312084011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 155975680 157286400 195952640 198901760 ⟨⟨105817161624, 105817161631⟩, ⟨101746304394, 109947037228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 155975680 157286400 198901760 201850880 ⟨⟨107261370137, 107261370145⟩, ⟨103181028238, 111400669126⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 157286400 190054400 201850880 t = true :=
  ⟨_, (join_su (m := 154664960) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 153354240) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 193003520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 153354240) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 198901760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 195952640) (by decide) (join_su (m := 155975680) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 193003520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 155975680) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 198901760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (29/128 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
