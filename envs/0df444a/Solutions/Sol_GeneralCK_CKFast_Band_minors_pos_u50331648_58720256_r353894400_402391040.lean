-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_58720256_r353894400_402391040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:19:24.205149+00:00
-- url     : https://prove2.me/submissions/005c9544-80a4-4bc5-b43b-58a8772dc17f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 7/100]`, `ρ ∈ [27/64, 307/640]` by 13 cells of the computing
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
theorem cell0 : cellOK 50331648 52428800 353894400 366018560 ⟨⟨337256318365, 337256318380⟩, ⟨318876351493, 356169469996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 52428800 54525952 353894400 366018560 ⟨⟨332536868003, 332536868019⟩, ⟨314452902082, 351145897409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 52428800 366018560 378142720 ⟨⟨344486955813, 344486955829⟩, ⟨326191970243, 363291939314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 52428800 54525952 366018560 378142720 ⟨⟨339753861658, 339753861674⟩, ⟨321746539105, 358264043500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 54525952 56623104 353894400 366018560 ⟨⟨327927795978, 327927795991⟩, ⟨310130947080, 346241668542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 56623104 58720256 353894400 366018560 ⟨⟨323424176034, 323424176049⟩, ⟨305906001822, 341451425896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 54525952 56623104 366018560 378142720 ⟨⟨335128777469, 335128777484⟩, ⟨317400700379, 353352613631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 56623104 58720256 366018560 378142720 ⟨⟨330606943381, 330606943396⟩, ⟨313150107112, 348552489305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 50331648 54525952 378142720 390266880 ⟨⟨349219550462, 349219550467⟩, ⟨322170484138, 377398210259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 50331648 54525952 390266880 402391040 ⟨⟨356227407238, 356227407246⟩, ⟨329258159457, 384280636659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 54525952 56623104 378142720 390266880 ⟨⟨342221072955, 342221072970⟩, ⟨324561287647, 360356205296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 56623104 58720256 378142720 390266880 ⟨⟨337682736532, 337682736546⟩, ⟨320286993326, 355547614152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 54525952 58720256 390266880 402391040 ⟨⟨346921748930, 346921748943⟩, ⟨320714512941, 374190354099⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 58720256 353894400 402391040 t = true :=
  ⟨_, (join_sr (m := 378142720) (by decide) (join_su (m := 54525952) (by decide) (join_sr (m := 366018560) (by decide) (join_su (m := 52428800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 52428800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 366018560) (by decide) (join_su (m := 56623104) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 56623104) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 54525952) (by decide) (join_sr (m := 390266880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 390266880) (by decide) (join_su (m := 56623104) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (27/64 : ℝ) (307/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  have e3 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
