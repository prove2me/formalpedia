-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_67108864_r644874240_741867520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:21:51.250499+00:00
-- url     : https://prove2.me/submissions/9fda5a84-48d1-421b-9f40-0f66ee8f712c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 2/25]`, `ρ ∈ [123/160, 283/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 54525952 644874240 669122560 ⟨⟨489541722148, 489541722154⟩, ⟨456553679943, 523150427708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 54525952 58720256 644874240 669122560 ⟨⟨480039484542, 480039484556⟩, ⟨447661135765, 513067411576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 54525952 669122560 693370880 ⟨⟨500832383480, 500832383490⟩, ⟨468029838430, 534174784961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 54525952 58720256 669122560 693370880 ⟨⟨491325199141, 491325199156⟩, ⟨459103506378, 524118790985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 58720256 62914560 644874240 669122560 ⟨⟨470788531425, 470788531440⟩, ⟨438999905532, 503251865925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 62914560 67108864 644874240 669122560 ⟨⟨461771057330, 461771057343⟩, ⟨430553926109, 493684734281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 58720256 62914560 669122560 693370880 ⟨⟨482059803155, 482059803170⟩, ⟨450400822884, 514318911863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 62914560 67108864 669122560 693370880 ⟨⟨473019099825, 473019099840⟩, ⟨441906307903, 504756917778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 50331648 54525952 693370880 717619200 ⟨⟨512006474838, 512006474845⟩, ⟨479381609617, 545093710105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 54525952 58720256 693370880 717619200 ⟨⟨502494585006, 502494585020⟩, ⟨470423105038, 535063300789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 50331648 54525952 717619200 741867520 ⟨⟨523076317829, 523076317837⟩, ⟨490621510625, 555918951181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 54525952 58720256 717619200 741867520 ⟨⟨513559718470, 513559718484⟩, ⟨481632100393, 545912586176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 58720256 62914560 693370880 717619200 ⟨⟨493215399264, 493215399281⟩, ⟨461680846274, 525278229455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 62914560 67108864 693370880 717619200 ⟨⟨484152478537, 484152478551⟩, ⟨453139897308, 515721025439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 58720256 62914560 717619200 741867520 ⟨⟨504267122284, 504267122301⟩, ⟨472851783300, 536141313114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 62914560 67108864 717619200 741867520 ⟨⟨495182699374, 495182699390⟩, ⟨464266132024, 526588360904⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 67108864 644874240 741867520 t = true :=
  ⟨_, (join_sr (m := 693370880) (by decide) (join_su (m := 58720256) (by decide) (join_sr (m := 669122560) (by decide) (join_su (m := 54525952) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 54525952) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 669122560) (by decide) (join_su (m := 62914560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 62914560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 58720256) (by decide) (join_sr (m := 717619200) (by decide) (join_su (m := 54525952) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 54525952) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 717619200) (by decide) (join_su (m := 62914560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 62914560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (123/160 : ℝ) (283/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((644874240 : ℤ) : ℝ) / (D : ℝ)) = (123/160 : ℝ) := by norm_num [D]
  have e3 : (((741867520 : ℤ) : ℝ) / (D : ℝ)) = (283/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
