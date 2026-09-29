-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:23.744169+00:00
-- url     : https://prove2.me/submissions/fcaa42fa-23e2-4f12-bed3-984c3d71fa5e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 181534720 184320000 ⟨⟨91564100624, 91564100632⟩, ⟨87800528987, 95380551993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 169082880 184320000 187105280 ⟨⟨92858518007, 92858518015⟩, ⟨89086103154, 96683788280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 169082880 170393600 181534720 184320000 ⟨⟨90808913414, 90808913422⟩, ⟨87066853010, 94603365537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 169082880 170393600 184320000 187105280 ⟨⟨92094094468, 92094094476⟩, ⟨88343221815, 95897337084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 169082880 187105280 189890560 ⟨⟨94150406231, 94150406238⟩, ⟨90369177698, 97984465370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167772160 169082880 189890560 192675840 ⟨⟨95439782943, 95439782949⟩, ⟨91649770010, 99282601162⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 169082880 170393600 187105280 189890560 ⟨⟨93376799893, 93376799899⟩, ⟨89617143681, 97188803809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 169082880 170393600 189890560 192675840 ⟨⟨94657046819, 94657046825⟩, ⟨90888635504, 98477783089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 170393600 171704320 181534720 184320000 ⟨⟨90060111056, 90060111062⟩, ⟨86339289637, 93832844167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 171704320 184320000 187105280 ⟨⟨91336103092, 91336103099⟩, ⟨87606500805, 95117597792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 171704320 173015040 181534720 184320000 ⟨⟨89317583316, 89317583323⟩, ⟨85617733812, 93068872307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 171704320 173015040 184320000 187105280 ⟨⟨90584433185, 90584433192⟩, ⟨86875834585, 94344454391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 170393600 171704320 187105280 189890560 ⟨⟨92609671985, 92609671992⟩, ⟨88871316700, 96399899910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 170393600 171704320 189890560 192675840 ⟨⟨93880834369, 93880834376⟩, ⟨90133753725, 97679767387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 171704320 173015040 187105280 189890560 ⟨⟨91848911376, 91848911384⟩, ⟨88131590746, 95617637243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 171704320 173015040 189890560 192675840 ⟨⟨93111034038, 93111034044⟩, ⟨89385018221, 96888437239⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 181534720 192675840 t = true :=
  ⟨_, (join_su (m := 170393600) (by decide) (join_sr (m := 187105280) (by decide) (join_su (m := 169082880) (by decide) (join_sr (m := 184320000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 184320000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 169082880) (by decide) (join_sr (m := 189890560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 189890560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 187105280) (by decide) (join_su (m := 171704320) (by decide) (join_sr (m := 184320000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 184320000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 171704320) (by decide) (join_sr (m := 189890560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 189890560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
