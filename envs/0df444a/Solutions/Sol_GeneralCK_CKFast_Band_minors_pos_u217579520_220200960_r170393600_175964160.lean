-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_220200960_r170393600_175964160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:33:44.715323+00:00
-- url     : https://prove2.me/submissions/ba452e4b-903d-4004-a205-ebff8cd542bc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 21/80]`, `ρ ∈ [13/64, 537/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 217579520 218234880 170393600 171786240 ⟨⟨62564326873, 62564326876⟩, ⟨61022882187, 64115442634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 217579520 218234880 171786240 173178880 ⟨⟨63054266517, 63054266520⟩, ⟨61510929304, 64607279150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 218234880 218890240 170393600 171786240 ⟨⟨62293250238, 62293250243⟩, ⟨60755286966, 63840849376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 218234880 218890240 171786240 173178880 ⟨⟨62781220948, 62781220953⟩, ⟨61241369862, 64330712293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 217579520 218234880 173178880 174571520 ⟨⟨63543927396, 63543927397⟩, ⟨61998698668, 65098835868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 217579520 218234880 174571520 175964160 ⟨⟨64033310240, 64033310243⟩, ⟨62486191014, 65590113524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218234880 218890240 173178880 174571520 ⟨⟨63268916200, 63268916206⟩, ⟨61727178293, 64820298743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218234880 218890240 174571520 175964160 ⟨⟨63756336715, 63756336722⟩, ⟨62212712977, 65309609453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 218890240 219545600 170393600 171786240 ⟨⟨62023012881, 62023012886⟩, ⟨60488513029, 63567113632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 218890240 219545600 171786240 173178880 ⟨⟨62509018935, 62509018942⟩, ⟨60972635980, 64055007231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 219545600 220200960 170393600 171786240 ⟨⟨61753608410, 61753608415⟩, ⟨60222554123, 63294228868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 219545600 220200960 171786240 173178880 ⟨⟨62237654064, 62237654069⟩, ⟨60704721380, 63780157407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218890240 219545600 173178880 174571520 ⟨⟨62994752808, 62994752813⟩, ⟨61456487719, 64542627663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218890240 219545600 174571520 175964160 ⟨⟨63480215208, 63480215215⟩, ⟨61940068953, 65029975640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 219545600 220200960 173178880 174571520 ⟨⟨62721430778, 62721430783⟩, ⟨61186620645, 64265816043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219545600 220200960 174571520 175964160 ⟨⟨63204939252, 63204939257⟩, ⟨61668252614, 64751205480⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 220200960 170393600 175964160 t = true :=
  ⟨_, (join_su (m := 218890240) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 218234880) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 171786240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 218234880) (by decide) (join_sr (m := 174571520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 174571520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 173178880) (by decide) (join_su (m := 219545600) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 171786240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 219545600) (by decide) (join_sr (m := 174571520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 174571520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (537/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
