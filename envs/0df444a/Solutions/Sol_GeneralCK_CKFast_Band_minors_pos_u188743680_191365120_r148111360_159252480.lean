-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_191365120_r148111360_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:40:53.767473+00:00
-- url     : https://prove2.me/submissions/bc8fb26e-e7c3-44f8-8752-aaa76fbd565f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 73/320]`, `ρ ∈ [113/640, 243/1280]` by 19 cells of the computing
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
theorem cell0 : cellOK 188743680 189399040 148111360 150896640 ⟨⟨66362065194, 66362065201⟩, ⟨64326954144, 68414361377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 189399040 190054400 148111360 149504000 ⟨⟨65787920356, 65787920363⟩, ⟨64111356868, 67475909832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 189399040 190054400 149504000 150896640 ⟨⟨66374462845, 66374462852⟩, ⟨64695764539, 68064588882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 188743680 189399040 150896640 153681920 ⟨⟨67538716398, 67538716406⟩, ⟨65498872056, 69595741783⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 189399040 190054400 150896640 153681920 ⟨⟨67253375748, 67253375754⟩, ⟨65219602431, 69304245682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 190054400 190709760 148111360 149504000 ⟨⟨65509336119, 65509336127⟩, ⟨63837104166, 67192944389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 190054400 190709760 149504000 150896640 ⟨⟨66093615869, 66093615876⟩, ⟨64419254445, 67779355445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 190709760 191365120 148111360 149504000 ⟨⟨65231836630, 65231836636⟩, ⟨63563910447, 66911089851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 190709760 191365120 149504000 150896640 ⟨⟨65813859972, 65813859978⟩, ⟨64143809667, 67495239240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 190054400 190709760 150896640 153681920 ⟨⟨66969144852, 66969144858⟩, ⟨64941408136, 69013894426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 190709760 191365120 150896640 153681920 ⟨⟨66686014424, 66686014431⟩, ⟨64664280193, 68724678412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 188743680 189399040 153681920 156467200 ⟨⟨68713431928, 68713431936⟩, ⟨66668867676, 70775172999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 189399040 190054400 153681920 156467200 ⟨⟨68423585874, 68423585881⟩, ⟨66385105257, 70479159221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 188743680 189399040 156467200 159252480 ⟨⟨69886223797, 69886223804⟩, ⟨67836952917, 71952667145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 189399040 190054400 156467200 159252480 ⟨⟨69591893989, 69591893996⟩, ⟨67548719141, 71652157554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 190054400 190709760 153681920 156467200 ⟨⟨68134861980, 68134861986⟩, ⟨66102430575, 70184302684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 190709760 191365120 153681920 156467200 ⟨⟨67847250882, 67847250889⟩, ⟨65820834578, 69890593712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 190054400 190709760 156467200 159252480 ⟨⟨69298698526, 69298698533⟩, ⟨67261585292, 71352817379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 190709760 191365120 156467200 159252480 ⟨⟨69006627971, 69006627977⟩, ⟨66975542245, 71054636867⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 191365120 148111360 159252480 t = true :=
  ⟨_, (join_sr (m := 153681920) (by decide) (join_su (m := 190054400) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell0) (join_sr (m := 149504000) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 189399040) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 150896640) (by decide) (join_su (m := 190709760) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 149504000) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 190709760) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_su (m := 190054400) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 189399040) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 156467200) (by decide) (join_su (m := 190709760) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 190709760) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (73/320 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
