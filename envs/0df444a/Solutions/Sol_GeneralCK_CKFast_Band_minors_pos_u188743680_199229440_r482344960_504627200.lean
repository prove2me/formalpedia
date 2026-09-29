-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r482344960_504627200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:53:30.39781+00:00
-- url     : https://prove2.me/submissions/76261a8a-2696-4b2b-8a31-a481d37ab1c8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [23/40, 77/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 482344960 487915520 ⟨⟨196004472915, 196004472922⟩, ⟨187533131876, 204654320775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 191365120 487915520 493486080 ⟨⟨198018558860, 198018558863⟩, ⟨189519448534, 206695943494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 193986560 482344960 487915520 ⟨⟨193184260547, 193184260556⟩, ⟨184787944656, 201757627112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 487915520 493486080 ⟨⟨195175569381, 195175569389⟩, ⟨186751453156, 203776534556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 191365120 493486080 499056640 ⟨⟨200029073436, 200029073442⟩, ⟨191502258409, 208733925052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 191365120 499056640 504627200 ⟨⟨202036063567, 202036063573⟩, ⟨193481607447, 210768313339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 193986560 493486080 499056640 ⟨⟨197163434672, 197163434680⟩, ⟨188711579209, 205791932203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 191365120 193986560 499056640 504627200 ⟨⟨199147901270, 199147901280⟩, ⟨190668366759, 207803865817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 196608000 482344960 487915520 ⟨⟨190388492948, 190388492957⟩, ⟨182066088978, 198886508624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 193986560 196608000 487915520 493486080 ⟨⟨192356978350, 192356978358⟩, ⟨184006754919, 200882641450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 199229440 482344960 487915520 ⟨⟨187616574040, 187616574049⟩, ⟨179366995253, 196040342624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 196608000 199229440 487915520 493486080 ⟨⟨189562193204, 189562193211⟩, ⟨181284787273, 198013645518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 493486080 499056640 ⟨⟨194322144811, 194322144820⟩, ⟨185944159586, 202875392580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193986560 196608000 499056640 504627200 ⟨⟨196284035197, 196284035205⟩, ⟨187878344988, 204864805732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 199229440 493486080 499056640 ⟨⟨191504614852, 191504614861⟩, ⟨183199436069, 199983691593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 499056640 504627200 ⟨⟨193443879936, 193443879945⟩, ⟨185110981794, 201950522592⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 482344960 504627200 t = true :=
  ⟨_, (join_su (m := 193986560) (by decide) (join_sr (m := 493486080) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 487915520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 487915520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 191365120) (by decide) (join_sr (m := 499056640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 499056640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 493486080) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 487915520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 487915520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 196608000) (by decide) (join_sr (m := 499056640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 499056640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (23/40 : ℝ) (77/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  have e3 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
