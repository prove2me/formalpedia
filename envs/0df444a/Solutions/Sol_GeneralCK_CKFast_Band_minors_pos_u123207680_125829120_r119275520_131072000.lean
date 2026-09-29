-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u123207680_125829120_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:20:38.829131+00:00
-- url     : https://prove2.me/submissions/91c9a72b-144a-48da-b2bd-72291c841afb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/320, 3/20]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 123207680 123863040 119275520 122224640 ⟨⟨84168307887, 84168307897⟩, ⟨81270729045, 87099317349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 123863040 124518400 119275520 122224640 ⟨⟨83774456591, 83774456601⟩, ⟨80889290639, 86692803779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 123207680 123863040 122224640 125173760 ⟨⟨86044908619, 86044908626⟩, ⟨83140534732, 88982610459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 123863040 124518400 122224640 125173760 ⟨⟨85643662657, 85643662664⟩, ⟨82751711910, 88568694120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 124518400 125173760 119275520 122224640 ⟨⟨83383218043, 83383218052⟩, ⟨80510357375, 86289013503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 125173760 125829120 119275520 122224640 ⟨⟨82994561290, 82994561299⟩, ⟨80133899737, 85887914081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 124518400 125173760 122224640 125173760 ⟨⟨85245062525, 85245062533⟩, ⟨82365427601, 88157533827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 125173760 125829120 122224640 125173760 ⟨⟨84849077030, 84849077037⟩, ⟨81981652038, 87749096911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 123207680 123863040 125173760 128122880 ⟨⟨87914276495, 87914276502⟩, ⟨85003181984, 90858596221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 123863040 124518400 125173760 128122880 ⟨⟨87505718551, 87505718560⟩, ⟨84607056397, 90437360821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 123207680 123863040 128122880 131072000 ⟨⟨89776488572, 89776488579⟩, ⟨86858746647, 92727352904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 123863040 124518400 128122880 131072000 ⟨⟨89360700036, 89360700045⟩, ⟨86455398679, 92298880833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 124518400 125173760 125173760 128122880 ⟨⟨87099838516, 87099838525⟩, ⟨84213501702, 90018913204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 125173760 125829120 125173760 128122880 ⟨⟨86696604972, 86696604980⟩, ⟨83822487901, 89603220483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 124518400 125173760 128122880 131072000 ⟨⟨88947620511, 88947620519⟩, ⟨86054653017, 91873227287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 125173760 125829120 128122880 131072000 ⟨⟨88537218360, 88537218370⟩, ⟨85656479438, 91450359183⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 123207680 125829120 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 124518400) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 123863040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 123863040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 125173760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 125173760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 124518400) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 123863040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 123863040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 125173760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 125173760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/320 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((123207680 : ℤ) : ℝ) / (D : ℝ)) = (47/320 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
