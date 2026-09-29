-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u149422080_152043520_r107479040_113377280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:09:34.960611+00:00
-- url     : https://prove2.me/submissions/ebd8559e-41b7-4248-a8cc-1d5f8d9a9af8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [57/320, 29/160]`, `ρ ∈ [41/320, 173/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 149422080 150077440 107479040 108953600 ⟨⟨63314859183, 63314859190⟩, ⟨61360913338, 65284899647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149422080 150077440 108953600 110428160 ⟨⟨64127617493, 64127617501⟩, ⟨62170847914, 66100474044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 150077440 150732800 107479040 108953600 ⟨⟨63032587646, 63032587653⟩, ⟨61085090698, 64996083966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 150077440 150732800 108953600 110428160 ⟨⟨63842103411, 63842103417⟩, ⟨61891790687, 65808408130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 149422080 150077440 110428160 111902720 ⟨⟨64939180279, 64939180286⟩, ⟨62979595340, 66914844487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 149422080 150077440 111902720 113377280 ⟨⟨65749552797, 65749552805⟩, ⟨63787160823, 67728016283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 150077440 150732800 110428160 111902720 ⟨⟨64650437350, 64650437356⟩, ⟨62697317097, 66619542167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 150077440 150732800 111902720 113377280 ⟨⟨65457594634, 65457594642⟩, ⟨63501675052, 67429491295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 150732800 151388160 107479040 108953600 ⟨⟨62751882748, 62751882756⟩, ⟨60810785807, 64708884782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 150732800 151388160 108953600 110428160 ⟨⟨63558169659, 63558169665⟩, ⟨61614264900, 65517972401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 151388160 152043520 107479040 108953600 ⟨⟨62472728185, 62472728192⟩, ⟨60537982926, 64423285219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 151388160 152043520 108953600 110428160 ⟨⟨63275799823, 63275799830⟩, ⟨61338254706, 65229149868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 150732800 151388160 110428160 111902720 ⟨⟨64363288283, 64363288289⟩, ⟨62416583830, 66325883554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 150732800 151388160 111902720 113377280 ⟨⟨65167243705, 65167243713⟩, ⟨63217747636, 67132623377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 151388160 152043520 110428160 111902720 ⟨⟨64077716556, 64077716562⟩, ⟨62137379581, 66033851556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 151388160 152043520 111902720 113377280 ⟨⟨64878483387, 64878483395⟩, ⟨62935362511, 66837395333⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 149422080 152043520 107479040 113377280 t = true :=
  ⟨_, (join_su (m := 150732800) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 150077440) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 108953600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 150077440) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 111902720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 110428160) (by decide) (join_su (m := 151388160) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 108953600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 151388160) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 111902720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (57/320 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (173/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
