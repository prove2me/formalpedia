-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r705167360_749731840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:04:00.490148+00:00
-- url     : https://prove2.me/submissions/47e7baaf-9055-4805-9717-51ad02cae38f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [269/320, 143/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 705167360 716308480 ⟨⟨275162982496, 275162982503⟩, ⟨264026852903, 286526704662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 191365120 193986560 705167360 716308480 ⟨⟨271503720284, 271503720294⟩, ⟨260465440910, 282768937955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 191365120 716308480 727449600 ⟨⟨278967344079, 278967344086⟩, ⟨267777109434, 290383645596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 716308480 727449600 ⟨⟨275270129423, 275270129433⟩, ⟨264177420506, 286588345992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 196608000 705167360 716308480 ⟨⟨267865109326, 267865109339⟩, ⟨256923835646, 279032636007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 196608000 199229440 705167360 716308480 ⟨⟨264246709732, 264246709742⟩, ⟨253401609805, 275317347673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 193986560 196608000 716308480 727449600 ⟨⟨271593307424, 271593307435⟩, ⟨260597310780, 282814219072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 196608000 199229440 716308480 727449600 ⟨⟨267936445893, 267936445903⟩, ⟨257036359819, 279060822272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 191365120 727449600 738590720 ⟨⟨282764028979, 282764028986⟩, ⟨271519844994, 294232728673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 191365120 193986560 727449600 738590720 ⟨⟨279029105427, 279029105436⟩, ⟨267882115324, 290400147130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 191365120 738590720 749731840 ⟨⟨286553307396, 286553307403⟩, ⟨275255322929, 298074230692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 191365120 193986560 738590720 749731840 ⟨⟨282780908554, 282780908565⟩, ⟨271579779075, 294204607946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 727449600 738590720 ⟨⟨275314311692, 275314311703⟩, ⟨264263733011, 286588442090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 199229440 727449600 738590720 ⟨⟨271619223244, 271619223253⟩, ⟨260664284449, 282797179497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 193986560 196608000 738590720 749731840 ⟨⟨279028372715, 279028372725⟩, ⟨267923346658, 290355561679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 738590720 749731840 ⟨⟨275295282949, 275295282959⟩, ⟨264285618881, 286526666272⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 705167360 749731840 t = true :=
  ⟨_, (join_sr (m := 727449600) (by decide) (join_su (m := 193986560) (by decide) (join_sr (m := 716308480) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 191365120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 716308480) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 196608000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 193986560) (by decide) (join_sr (m := 738590720) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 191365120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 738590720) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 196608000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (269/320 : ℝ) (143/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  have e3 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
