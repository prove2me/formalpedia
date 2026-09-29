-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r682885120_705167360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:04:08.480011+00:00
-- url     : https://prove2.me/submissions/32b037bd-9515-492a-abeb-92acb34e40be

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [521/640, 269/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 682885120 688455680 ⟨⟨225003290257, 225003290265⟩, ⟨216390025480, 233778617712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 688455680 694026240 ⟨⟨226676684619, 226676684628⟩, ⟨218036682939, 235478665674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 682885120 688455680 ⟨⟨221656976067, 221656976077⟩, ⟨213108522119, 230367016787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 688455680 694026240 ⟨⟨223309818318, 223309818327⟩, ⟨214734633220, 232046530701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 694026240 699596800 ⟨⟨228348701456, 228348701465⟩, ⟨219681975539, 237177318839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 699596800 705167360 ⟨⟨230019362309, 230019362318⟩, ⟨221325924448, 238874599108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 694026240 699596800 ⟨⟨224961335728, 224961335737⟩, ⟨216359430416, 233724704344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 699596800 705167360 ⟨⟨226611548917, 226611548926⟩, ⟨217982933976, 235401558672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 682885120 688455680 ⟨⟨218327025626, 218327025634⟩, ⟨209842841244, 226972311194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 688455680 694026240 ⟨⟨219959231695, 219959231704⟩, ⟨211448331107, 228631197157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 230686720 682885120 688455680 ⟨⟨215013088590, 215013088593⟩, ⟨206592641443, 223594142100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228065280 230686720 688455680 694026240 ⟨⟨216624577045, 216624577049⟩, ⟨208177437595, 225232309093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 225443840 228065280 694026240 699596800 ⟨⟨221590164340, 221590164349⟩, ⟨213052556785, 230288796080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 228065280 699596800 705167360 ⟨⟨223219843289, 223219843298⟩, ⟨214655537671, 231945128001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 230686720 694026240 699596800 ⟨⟨218234842234, 218234842239⟩, ⟨209761018048, 226869240986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 230686720 699596800 705167360 ⟨⟨219843903016, 219843903021⟩, ⟨211343401352, 228504956929⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 682885120 705167360 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 694026240) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 688455680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 688455680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 699596800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 699596800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 694026240) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 688455680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 688455680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 228065280) (by decide) (join_sr (m := 699596800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 699596800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (521/640 : ℝ) (269/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((682885120 : ℤ) : ℝ) / (D : ℝ)) = (521/640 : ℝ) := by norm_num [D]
  have e3 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
