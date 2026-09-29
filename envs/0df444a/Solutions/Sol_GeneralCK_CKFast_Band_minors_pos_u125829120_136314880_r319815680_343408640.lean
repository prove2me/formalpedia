-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r319815680_343408640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:44:33.389758+00:00
-- url     : https://prove2.me/submissions/cfa99c9b-6c9c-48a6-bf11-33560c25641f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [61/160, 131/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 319815680 325713920 ⟨⟨195081579673, 195081579681⟩, ⟨184967375157, 205463111415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 125829120 128450560 325713920 331612160 ⟨⟨198070680637, 198070680648⟩, ⟨187926970230, 208480161828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 128450560 131072000 319815680 325713920 ⟨⟨192135687175, 192135687183⟩, ⟨182150712483, 202383562242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 325713920 331612160 ⟨⟨195094325660, 195094325671⟩, ⟨185079418400, 205370679523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 125829120 128450560 331612160 337510400 ⟨⟨201045809051, 201045809061⟩, ⟨190872915286, 211482916250⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 125829120 128450560 337510400 343408640 ⟨⟨204007213152, 204007213162⟩, ⟨193805450555, 214471631036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 128450560 131072000 331612160 337510400 ⟨⟨198039458128, 198039458139⟩, ⟨187994930974, 208343976280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 128450560 131072000 337510400 343408640 ⟨⟨200971321070, 200971321080⟩, ⟨190897479128, 211303696679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 131072000 133693440 319815680 325713920 ⟨⟨189240280048, 189240280056⟩, ⟨179381276027, 199357878739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 131072000 133693440 325713920 331612160 ⟨⟨192168425331, 192168425342⟩, ⟨182279103933, 202314985055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133693440 136314880 319815680 325713920 ⟨⟨186393638257, 186393638265⟩, ⟨176657469158, 196384213258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 133693440 136314880 325713920 331612160 ⟨⟨189291272430, 189291272438⟩, ⟨179524440402, 199311246502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131072000 133693440 331612160 337510400 ⟨⟨195083518482, 195083518492⟩, ⟨185164182456, 205258733844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 131072000 133693440 337510400 343408640 ⟨⟨197985784775, 197985784786⟩, ⟨188036729721, 208189357635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 133693440 136314880 331612160 337510400 ⟨⟨192176295926, 192176295936⟩, ⟨182379093764, 202225372916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 136314880 337510400 343408640 ⟨⟨195048923322, 195048923332⟩, ⟨185221637077, 205126813921⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 319815680 343408640 t = true :=
  ⟨_, (join_su (m := 131072000) (by decide) (join_sr (m := 331612160) (by decide) (join_su (m := 128450560) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 325713920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 128450560) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 337510400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 331612160) (by decide) (join_su (m := 133693440) (by decide) (join_sr (m := 325713920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 325713920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 133693440) (by decide) (join_sr (m := 337510400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 337510400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (61/160 : ℝ) (131/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  have e3 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
