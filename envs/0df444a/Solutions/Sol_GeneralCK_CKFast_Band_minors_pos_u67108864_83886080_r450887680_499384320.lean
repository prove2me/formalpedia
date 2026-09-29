-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_83886080_r450887680_499384320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:57:55.959498+00:00
-- url     : https://prove2.me/submissions/e68d09b7-5099-4bc5-9ffb-967086285eda

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 1/10]`, `ρ ∈ [43/80, 381/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 71303168 450887680 463011840 ⟨⟨354275193008, 354275193023⟩, ⟨330177847271, 379214069917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 71303168 463011840 475136000 ⟨⟨360667568468, 360667568482⟩, ⟨336585185855, 385563583380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 71303168 75497472 450887680 463011840 ⟨⟨346126129334, 346126129349⟩, ⟨322579321182, 370502954997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 71303168 75497472 463011840 475136000 ⟨⟨352481108953, 352481108967⟩, ⟨328937596901, 376828642733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 71303168 475136000 487260160 ⟨⟨366994330789, 366994330803⟩, ⟨342927273939, 391847796312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 71303168 487260160 499384320 ⟨⟨373258526910, 373258526924⟩, ⟨349207068618, 398069812481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 71303168 75497472 475136000 487260160 ⟨⟨358772376259, 358772376272⟩, ⟨335232761909, 383090598310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 71303168 75497472 487260160 499384320 ⟨⟨365002828994, 365002829007⟩, ⟨341467619394, 389291786673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 79691776 450887680 463011840 ⟨⟨338236515053, 338236515066⟩, ⟨315216373689, 362074751437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 75497472 79691776 463011840 475136000 ⟨⟨344549496336, 344549496349⟩, ⟨321522010897, 368370867602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79691776 83886080 450887680 463011840 ⟨⟨330589512424, 330589512437⟩, ⟨308073917945, 353911000495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 79691776 83886080 463011840 475136000 ⟨⟨336856354223, 336856354237⟩, ⟨314323711638, 360172358436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 75497472 79691776 475136000 487260160 ⟨⟨350800721936, 350800721947⟩, ⟨327766689449, 374604929694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 75497472 79691776 487260160 499384320 ⟨⟨356992943425, 356992943439⟩, ⟨333953063760, 380779763895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 79691776 83886080 475136000 487260160 ⟨⟨343063434386, 343063434400⟩, ⟨320514698478, 366373424788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 79691776 83886080 487260160 499384320 ⟨⟨349213362065, 349213362078⟩, ⟨326649389532, 372516888297⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 83886080 450887680 499384320 t = true :=
  ⟨_, (join_su (m := 75497472) (by decide) (join_sr (m := 475136000) (by decide) (join_su (m := 71303168) (by decide) (join_sr (m := 463011840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 463011840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 71303168) (by decide) (join_sr (m := 487260160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 487260160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 475136000) (by decide) (join_su (m := 79691776) (by decide) (join_sr (m := 463011840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 463011840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 79691776) (by decide) (join_sr (m := 487260160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 487260160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (43/80 : ℝ) (381/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((450887680 : ℤ) : ℝ) / (D : ℝ)) = (43/80 : ℝ) := by norm_num [D]
  have e3 : (((499384320 : ℤ) : ℝ) / (D : ℝ)) = (381/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
