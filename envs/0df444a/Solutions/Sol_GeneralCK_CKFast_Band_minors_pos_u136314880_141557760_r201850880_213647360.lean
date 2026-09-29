-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_141557760_r201850880_213647360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:34:44.603743+00:00
-- url     : https://prove2.me/submissions/f8bcd479-c3b4-4db6-9e94-fcb2d89c8bc5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 27/160]`, `ρ ∈ [77/320, 163/640]` by 13 cells of the computing
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
theorem cell0 : cellOK 136314880 137625600 201850880 204800000 ⟨⟨123061860602, 123061860610⟩, ⟨118554387034, 127637971599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 137625600 204800000 207749120 ⟨⟨124651673886, 124651673895⟩, ⟨120134639337, 129237210487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 137625600 138936320 201850880 204800000 ⟨⟨122037517773, 122037517782⟩, ⟨117560743687, 126582195019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 137625600 138936320 204800000 207749120 ⟨⟨123616850487, 123616850496⟩, ⟨119130515661, 128170959119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 137625600 207749120 213647360 ⟨⟨127028136073, 127028136081⟩, ⟨121374232189, 132789150191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 137625600 138936320 207749120 213647360 ⟨⟨125977757272, 125977757281⟩, ⟨120365860055, 131695530934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 138936320 140247040 201850880 204800000 ⟨⟨121023556847, 121023556855⟩, ⟨116577035839, 125537260167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 138936320 140247040 204800000 207749120 ⟨⟨122592457738, 122592457747⟩, ⟨118136378005, 127115596263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 140247040 141557760 201850880 204800000 ⟨⟨120019777792, 120019777798⟩, ⟨115603073178, 124502956963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 140247040 141557760 204800000 207749120 ⟨⟨121578295461, 121578295467⟩, ⟨117152035826, 126070911780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 138936320 140247040 207749120 213647360 ⟨⟨124937879090, 124937879098⟩, ⟨119367400814, 130613022216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 140247040 141557760 207749120 210698240 ⟨⟨123132662671, 123132662677⟩, ⟨118696902563, 127634661067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 140247040 141557760 210698240 213647360 ⟨⟨124682915651, 124682915653⟩, ⟨120237708972, 129194241702⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 141557760 201850880 213647360 t = true :=
  ⟨_, (join_su (m := 138936320) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 137625600) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 204800000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 137625600) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 207749120) (by decide) (join_su (m := 140247040) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 204800000) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 140247040) (by decide) (leaf_ok cell10) (join_sr (m := 210698240) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (163/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
