-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r353894400_402391040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:32:22.63386+00:00
-- url     : https://prove2.me/submissions/e755fd2d-f5d0-4f75-b656-d0c6ebc34348

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/25]`, `ρ ∈ [27/64, 307/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 20971520 353894400 366018560 ⟨⟨430143255966, 430143255987⟩, ⟨393463322382, 468231623067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 16777216 20971520 366018560 378142720 ⟨⟨437086474520, 437086474539⟩, ⟨400803057496, 474676862700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 20971520 25165824 353894400 366018560 ⟨⟨415353045118, 415353045137⟩, ⟨380287382361, 451839424069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 20971520 25165824 366018560 378142720 ⟨⟨422411257895, 422411257915⟩, ⟨387681627176, 458469018148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 16777216 20971520 378142720 390266880 ⟨⟨443911507164, 443911507180⟩, ⟨408009243989, 481025856537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 16777216 20971520 390266880 402391040 ⟨⟨450626345493, 450626345513⟩, ⟨415090691355, 487285169992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 20971520 25165824 378142720 390266880 ⟨⟨429348405852, 429348405870⟩, ⟨394942892058, 464995107485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 20971520 25165824 390266880 402391040 ⟨⟨436172470918, 436172470934⟩, ⟨402079704782, 471424631770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 25165824 29360128 353894400 366018560 ⟨⟨401628643422, 401628643440⟩, ⟨368000987679, 436667184751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 25165824 29360128 366018560 378142720 ⟨⟨408770636186, 408770636205⟩, ⟨375426787007, 443440864953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 29360128 33554432 353894400 366018560 ⟨⟨388811863819, 388811863836⟩, ⟨356484534617, 422528432282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 29360128 33554432 366018560 378142720 ⟨⟨396011825561, 396011825579⟩, ⟨363922832571, 429412893023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 25165824 29360128 378142720 390266880 ⟨⟨415790349692, 415790349710⟩, ⟨382721185199, 450106233983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 25165824 29360128 390266880 402391040 ⟨⟨422695636187, 422695636206⟩, ⟨389892374591, 456670398808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 29360128 33554432 378142720 390266880 ⟨⟨403089565670, 403089565685⟩, ⟨371232061408, 436186140200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 29360128 33554432 390266880 402391040 ⟨⟨410052724336, 410052724353⟩, ⟨378420045912, 442855298749⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 33554432 353894400 402391040 t = true :=
  ⟨_, (join_su (m := 25165824) (by decide) (join_sr (m := 378142720) (by decide) (join_su (m := 20971520) (by decide) (join_sr (m := 366018560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 366018560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 20971520) (by decide) (join_sr (m := 390266880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 390266880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 378142720) (by decide) (join_su (m := 29360128) (by decide) (join_sr (m := 366018560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 366018560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 29360128) (by decide) (join_sr (m := 390266880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 390266880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (27/64 : ℝ) (307/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  have e3 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
