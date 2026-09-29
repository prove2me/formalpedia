-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r727449600_749731840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:05:35.436989+00:00
-- url     : https://prove2.me/submissions/1e9b54ae-c650-4425-ae84-6a7ab760b9e7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [111/128, 143/160]` by 14 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 727449600 738590720 ⟨⟨253425170807, 253425170817⟩, ⟨242937224590, 264132993409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212336640 214958080 727449600 733020160 ⟨⟨248978329296, 248978329305⟩, ⟨239954199511, 258164478326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 214958080 733020160 738590720 ⟨⟨250701180544, 250701180555⟩, ⟨241650485990, 259913695786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 209715200 212336640 738590720 749731840 ⟨⟨256907586482, 256907586491⟩, ⟨246363950428, 267670220657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 214958080 738590720 744161280 ⟨⟨252422680920, 252422680930⟩, ⟨243345436104, 261661542791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 212336640 214958080 744161280 749731840 ⟨⟨254142853916, 254142853926⟩, ⟨245039072917, 263408043241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 214958080 217579520 727449600 733020160 ⟨⟨245420008876, 245420008881⟩, ⟨236462133543, 254539668687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214958080 217579520 733020160 738590720 ⟨⟨247123001132, 247123001136⟩, ⟨238138523939, 256269090844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 220200960 727449600 733020160 ⟨⟨241878373416, 241878373426⟩, ⟨232986263439, 250932016688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217579520 220200960 733020160 738590720 ⟨⟨243561404765, 243561404776⟩, ⟨234642665941, 252641530879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 217579520 738590720 744161280 ⟨⟨248824691149, 248824691152⟩, ⟨239813624985, 257997192896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 214958080 217579520 744161280 749731840 ⟨⟨250525101471, 250525101475⟩, ⟨241487458819, 259723997774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 220200960 738590720 744161280 ⟨⟨245243181466, 245243181475⟩, ⟨236297825082, 254349774261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 217579520 220200960 744161280 749731840 ⟨⟨246923725141, 246923725150⟩, ⟨237951762098, 256056768819⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 727449600 749731840 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 738590720) (by decide) (join_su (m := 212336640) (by decide) (leaf_ok cell0) (join_sr (m := 733020160) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 212336640) (by decide) (leaf_ok cell3) (join_sr (m := 744161280) (by decide) (leaf_ok cell4) (leaf_ok cell5)))) (join_sr (m := 738590720) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 733020160) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 733020160) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 217579520) (by decide) (join_sr (m := 744161280) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 744161280) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (111/128 : ℝ) (143/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((727449600 : ℤ) : ℝ) / (D : ℝ)) = (111/128 : ℝ) := by norm_num [D]
  have e3 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
