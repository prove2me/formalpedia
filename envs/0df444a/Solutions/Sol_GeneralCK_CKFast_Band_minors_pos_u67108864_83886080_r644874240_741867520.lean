-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_83886080_r644874240_741867520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T11:00:03.852003+00:00
-- url     : https://prove2.me/submissions/51c8f6c2-83db-4546-b739-74db13ba6d1d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 1/10]`, `ρ ∈ [123/160, 283/320]` by 17 cells of the computing
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
theorem cell0 : cellOK 67108864 71303168 644874240 669122560 ⟨⟨452971405841, 452971405855⟩, ⟨422308989035, 484349312863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 71303168 75497472 644874240 669122560 ⟨⟨444375691483, 444375691497⟩, ⟨414252431204, 475230826367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 71303168 669122560 693370880 ⟨⟨464188068726, 464188068740⟩, ⟨433606276053, 495416845751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 71303168 75497472 669122560 693370880 ⟨⟨455553397632, 455553397646⟩, ⟨425488535912, 486284588638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 75497472 79691776 644874240 669122560 ⟨⟨435971506627, 435971506641⟩, ⟨406372891255, 466316101129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 79691776 83886080 644874240 656998400 ⟨⟨424959800467, 424959800480⟩, ⟨402242673019, 448163962919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 79691776 83886080 656998400 669122560 ⟨⟨430528161034, 430528161048⟩, ⟨407800833605, 453724875381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 75497472 79691776 669122560 693370880 ⟨⟨447103198250, 447103198266⟩, ⟨417542153419, 477347578717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 79691776 83886080 669122560 693370880 ⟨⟨438826782516, 438826782530⟩, ⟨409757263041, 468594540160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 67108864 71303168 693370880 717619200 ⟨⟨475291391430, 475291391444⟩, ⟨444787061482, 506376406653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 71303168 75497472 693370880 717619200 ⟨⟨466619357340, 466619357354⟩, ⟨436610588773, 497230880683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 67108864 71303168 717619200 741867520 ⟨⟨486292565323, 486292565337⟩, ⟨455862407443, 517239075271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 71303168 75497472 717619200 741867520 ⟨⟨477584433717, 477584433731⟩, ⟨447629273306, 508080531050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 75497472 79691776 693370880 717619200 ⟨⟨458124970279, 458124970295⟩, ⟨428599945615, 488272437956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 79691776 83886080 693370880 717619200 ⟨⟨449797981728, 449797981742⟩, ⟨420745631357, 479490311879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 75497472 79691776 717619200 741867520 ⟨⟨469047347461, 469047347475⟩, ⟨439556572031, 499101234183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 79691776 83886080 717619200 741867520 ⟨⟨460671467672, 460671467689⟩, ⟨431635146020, 490290888948⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 83886080 644874240 741867520 t = true :=
  ⟨_, (join_sr (m := 693370880) (by decide) (join_su (m := 75497472) (by decide) (join_sr (m := 669122560) (by decide) (join_su (m := 71303168) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 71303168) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 669122560) (by decide) (join_su (m := 79691776) (by decide) (leaf_ok cell4) (join_sr (m := 656998400) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 79691776) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 75497472) (by decide) (join_sr (m := 717619200) (by decide) (join_su (m := 71303168) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 71303168) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 717619200) (by decide) (join_su (m := 79691776) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 79691776) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (123/160 : ℝ) (283/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((644874240 : ℤ) : ℝ) / (D : ℝ)) = (123/160 : ℝ) := by norm_num [D]
  have e3 : (((741867520 : ℤ) : ℝ) / (D : ℝ)) = (283/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
