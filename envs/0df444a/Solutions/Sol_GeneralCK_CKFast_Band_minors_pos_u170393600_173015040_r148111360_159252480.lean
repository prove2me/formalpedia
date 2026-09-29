-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u170393600_173015040_r148111360_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:59.63046+00:00
-- url     : https://prove2.me/submissions/5de2b5e8-e36d-4af5-a1c9-9e7a95dcba6e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/64, 33/160]`, `ρ ∈ [113/640, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 170393600 171048960 148111360 150896640 ⟨⟨74710994352, 74710994360⟩, ⟨72490883464, 76950968581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 171048960 171704320 148111360 150896640 ⟨⟨74395283617, 74395283625⟩, ⟨72182338304, 76627985349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 171048960 150896640 153681920 ⟨⟨76019870092, 76019870100⟩, ⟨73794671150, 78264916349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 171048960 171704320 150896640 153681920 ⟨⟨75699244576, 75699244582⟩, ⟨73481223585, 77937006485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 171704320 172359680 148111360 150896640 ⟨⟨74080973290, 74080973292⟩, ⟨71875148639, 76306448357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 172359680 173015040 148111360 150896640 ⟨⟨73768050802, 73768050810⟩, ⟨71569302348, 75986344586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 171704320 172359680 150896640 153681920 ⟨⟨75380034501, 75380034505⟩, ⟨73169146585, 77610557851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 172359680 173015040 150896640 153681920 ⟨⟨75062227210, 75062227218⟩, ⟨72858427934, 77285557344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 170393600 171048960 153681920 156467200 ⟨⟨77326097797, 77326097803⟩, ⟨75095831422, 79576195303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 171048960 171704320 153681920 156467200 ⟨⟨77000586655, 77000586662⟩, ⟨74777510308, 79243388267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 170393600 171048960 156467200 159252480 ⟨⟨78629695916, 78629695923⟩, ⟨76394382544, 80884824084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 171048960 171704320 156467200 159252480 ⟨⟨78299328027, 78299328033⟩, ⟨76071216456, 80547149052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 171704320 172359680 153681920 156467200 ⟨⟨76676505690, 76676505693⟩, ⟨74460574526, 78912057149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 172359680 173015040 153681920 156467200 ⟨⟨76353842151, 76353842159⟩, ⟨74145011775, 78582188757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 171704320 172359680 156467200 159252480 ⟨⟨77970404749, 77970404752⟩, ⟨75749450180, 80210964324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 172359680 173015040 156467200 159252480 ⟨⟨77642913247, 77642913255⟩, ⟨75429071321, 79876256624⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 170393600 173015040 148111360 159252480 t = true :=
  ⟨_, (join_sr (m := 153681920) (by decide) (join_su (m := 171704320) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 171048960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 171048960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 150896640) (by decide) (join_su (m := 172359680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 172359680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 171704320) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 171048960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 171048960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 156467200) (by decide) (join_su (m := 172359680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 172359680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/64 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
