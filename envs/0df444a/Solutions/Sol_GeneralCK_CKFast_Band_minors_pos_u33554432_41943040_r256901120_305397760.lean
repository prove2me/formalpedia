-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r256901120_305397760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:51:34.797383+00:00
-- url     : https://prove2.me/submissions/0e318422-ea2b-4455-9cfb-e237e55ebb4b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 1/20]`, `ρ ∈ [49/160, 233/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 33554432 35651584 256901120 269025280 ⟨⟨316374661435, 316374661454⟩, ⟨293674704834, 340023304032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 35651584 37748736 256901120 269025280 ⟨⟨310485465301, 310485465319⟩, ⟨288310843780, 333582655059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 33554432 35651584 269025280 281149440 ⟨⟨324937544113, 324937544132⟩, ⟨302451037826, 348318283303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 35651584 37748736 269025280 281149440 ⟨⟨319047038214, 319047038233⟩, ⟨297065476770, 341899902534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 37748736 39845888 256901120 269025280 ⟨⟨304806090384, 304806090399⟩, ⟨283132945670, 327376583799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 39845888 41943040 256901120 269025280 ⟨⟨299323186866, 299323186880⟩, ⟨278129405347, 321389982816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 37748736 39845888 269025280 281149440 ⟨⟨313360332646, 313360332664⟩, ⟨291861421718, 335708300627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 39845888 41943040 269025280 281149440 ⟨⟨307864681450, 307864681468⟩, ⟨286827732093, 329729130014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 33554432 35651584 281149440 293273600 ⟨⟨333289071811, 333289071830⟩, ⟨311010909631, 356410651133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 35651584 37748736 281149440 293273600 ⟨⟨327400383437, 327400383455⟩, ⟨305607857702, 350016255771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 33554432 35651584 293273600 305397760 ⟨⟨341444480348, 341444480368⟩, ⟨319369487331, 364315381531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 35651584 37748736 293273600 305397760 ⟨⟨335560248434, 335560248451⟩, ⟨313952595885, 357946309235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 37748736 39845888 281149440 293273600 ⟨⟨321709697862, 321709697879⟩, ⟨300381947435, 343841225557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 39845888 41943040 281149440 293273600 ⟨⟨316204829014, 316204829031⟩, ⟨295322474231, 337871910274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 37748736 39845888 293273600 305397760 ⟨⟨329868443179, 329868443196⟩, ⟨308708585315, 351789553874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 39845888 41943040 293273600 305397760 ⟨⟨324357398046, 324357398063⟩, ⟨303627160036, 345832106256⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 41943040 256901120 305397760 t = true :=
  ⟨_, (join_sr (m := 281149440) (by decide) (join_su (m := 37748736) (by decide) (join_sr (m := 269025280) (by decide) (join_su (m := 35651584) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 35651584) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 269025280) (by decide) (join_su (m := 39845888) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 39845888) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 37748736) (by decide) (join_sr (m := 293273600) (by decide) (join_su (m := 35651584) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 35651584) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 293273600) (by decide) (join_su (m := 39845888) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 39845888) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (49/160 : ℝ) (233/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  have e3 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
