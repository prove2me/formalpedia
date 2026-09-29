-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_83886080_r547880960_596377600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:58:32.012086+00:00
-- url     : https://prove2.me/submissions/23e6ce9d-ce30-4317-bd42-6ce22ec1adac

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 1/10]`, `ρ ∈ [209/320, 91/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 71303168 547880960 560005120 ⟨⟨403737550211, 403737550226⟩, ⟨379765597708, 428345004529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 71303168 560005120 572129280 ⟨⟨409682485126, 409682485140⟩, ⟨385726314726, 434250816858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 71303168 75497472 547880960 560005120 ⟨⟨395334938235, 395334938250⟩, ⟨371826600364, 419480163425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 71303168 75497472 560005120 572129280 ⟨⟨401254084122, 401254084137⟩, ⟨377751631240, 425371378186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 71303168 572129280 584253440 ⟨⟨415582444213, 415582444228⟩, ⟨391641901775, 440112257394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 71303168 584253440 596377600 ⟨⟨421439505037, 421439505052⟩, ⟨397514396665, 445931420611⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 71303168 75497472 572129280 584253440 ⟨⟨407129232682, 407129232696⟩, ⟨383632707924, 431218944973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 71303168 75497472 584253440 596377600 ⟨⟨412962380640, 412962380654⟩, ⟨389471782005, 437024886105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 79691776 547880960 560005120 ⟨⟨387156647202, 387156647216⟩, ⟨364095160063, 410855313233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 75497472 79691776 560005120 572129280 ⟨⟨393045902167, 393045902180⟩, ⟨369981135128, 416727042332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79691776 83886080 547880960 560005120 ⟨⟨379189054959, 379189054973⟩, ⟨356558822834, 402455826816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 79691776 83886080 560005120 572129280 ⟨⟨385044650888, 385044650902⟩, ⟨362402652352, 408303571193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 75497472 79691776 572129280 584253440 ⟨⟨398892204424, 398892204438⟩, ⟨375824368661, 422555947868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 75497472 79691776 584253440 596377600 ⟨⟨404697469622, 404697469638⟩, ⟨381626727204, 428343977921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 79691776 83886080 572129280 584253440 ⟨⟨390858391855, 390858391869⟩, ⟨368204980160, 414109400331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 79691776 83886080 584253440 596377600 ⟨⟨396632112779, 396632112795⟩, ⟨373967589303, 419875186855⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 83886080 547880960 596377600 t = true :=
  ⟨_, (join_su (m := 75497472) (by decide) (join_sr (m := 572129280) (by decide) (join_su (m := 71303168) (by decide) (join_sr (m := 560005120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 560005120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 71303168) (by decide) (join_sr (m := 584253440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 584253440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 572129280) (by decide) (join_su (m := 79691776) (by decide) (join_sr (m := 560005120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 560005120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 79691776) (by decide) (join_sr (m := 584253440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 584253440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (209/320 : ℝ) (91/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((547880960 : ℤ) : ℝ) / (D : ℝ)) = (209/320 : ℝ) := by norm_num [D]
  have e3 : (((596377600 : ℤ) : ℝ) / (D : ℝ)) = (91/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
