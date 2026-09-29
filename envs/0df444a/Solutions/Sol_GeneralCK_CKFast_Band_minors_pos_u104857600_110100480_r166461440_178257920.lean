-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_110100480_r166461440_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:27:06.10916+00:00
-- url     : https://prove2.me/submissions/200d26ac-dc0a-4e16-a91d-11e5f6ea3503

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 21/160]`, `ρ ∈ [127/640, 17/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 106168320 166461440 169410560 ⟨⟨128531493268, 128531493279⟩, ⟨123235322014, 133923430037⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 106168320 169410560 172359680 ⟨⟨130479792250, 130479792258⟩, ⟨125173537517, 135881443803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 106168320 107479040 166461440 169410560 ⟨⟨127332411024, 127332411034⟩, ⟨122082289658, 132676934061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 106168320 107479040 169410560 172359680 ⟨⟨129267191408, 129267191419⟩, ⟨124006936358, 134621494383⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 106168320 172359680 175308800 ⟨⟨132419889985, 132419889996⟩, ⟨127103673848, 137831134674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 106168320 175308800 178257920 ⟨⟨134351882413, 134351882422⟩, ⟨129025824728, 139772600825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 106168320 107479040 172359680 175308800 ⟨⟨131193944135, 131193944143⟩, ⟨125923674730, 136557908039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 106168320 107479040 175308800 178257920 ⟨⟨133112762105, 133112762113⟩, ⟨127832595545, 138486270090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 107479040 108789760 166461440 169410560 ⟨⟨126149869287, 126149869290⟩, ⟨120944937037, 131447871623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 108789760 169410560 172359680 ⟨⟨128071213082, 128071213088⟩, ⟨122856101865, 133379055008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 108789760 110100480 166461440 169410560 ⟨⟨124983466322, 124983466333⟩, ⟨119822886431, 130235815963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 108789760 110100480 169410560 172359680 ⟨⟨126891455536, 126891455547⟩, ⟨121720656061, 132153699195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 107479040 108789760 172359680 175308800 ⟨⟨129984699007, 129984699014⟩, ⟨124759525450, 135302264127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 107479040 108789760 175308800 178257920 ⟨⟨131890417036, 131890417042⟩, ⟨126655295718, 137217591027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 108789760 110100480 172359680 175308800 ⟨⟨128791752963, 128791752971⟩, ⟨123610847872, 134063776817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 108789760 110100480 175308800 178257920 ⟨⟨130684445742, 130684445752⟩, ⟨125493547040, 135966137969⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 110100480 166461440 178257920 t = true :=
  ⟨_, (join_su (m := 107479040) (by decide) (join_sr (m := 172359680) (by decide) (join_su (m := 106168320) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 169410560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 106168320) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 175308800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 172359680) (by decide) (join_su (m := 108789760) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 169410560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 108789760) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 175308800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (127/640 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
