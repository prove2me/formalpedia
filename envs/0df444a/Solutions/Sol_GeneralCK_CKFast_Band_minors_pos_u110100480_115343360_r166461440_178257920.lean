-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_115343360_r166461440_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:27:29.974625+00:00
-- url     : https://prove2.me/submissions/b092aff7-668e-4e40-9e09-e23665eadf06

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 11/80]`, `ρ ∈ [127/640, 17/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 110100480 111411200 166461440 169410560 ⟨⟨123832813537, 123832813547⟩, ⟨118715772346, 129040354381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 110100480 111411200 169410560 172359680 ⟨⟨125727530111, 125727530119⟩, ⟨120600233149, 130945014442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 111411200 112721920 166461440 169410560 ⟨⟨122697534895, 122697534905⟩, ⟨117623241025, 127861087618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 111411200 112721920 169410560 172359680 ⟨⟨124579060648, 124579060656⟩, ⟨119494479027, 129752601617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 110100480 111411200 172359680 175308800 ⟨⟨127614717359, 127614717369⟩, ⟨122477275987, 132842033895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 110100480 111411200 175308800 178257920 ⟨⟨129494459693, 129494459701⟩, ⟨124346983372, 134731499067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 111411200 112721920 172359680 175308800 ⟨⟨126453216007, 126453216017⟩, ⟨121358455430, 131636636440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 111411200 112721920 175308800 178257920 ⟨⟨128320082745, 128320082755⟩, ⟨123215250173, 133513275700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 112721920 114032640 166461440 169410560 ⟨⟨121577266426, 121577266437⟩, ⟨116544949965, 126697629322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 112721920 114032640 169410560 172359680 ⟨⟨123445683001, 123445683012⟩, ⟨118403050805, 128576074430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 114032640 115343360 166461440 169410560 ⟨⟨120471655726, 120471655728⟩, ⟨115480567459, 125549605510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 114032640 115343360 169410560 172359680 ⟨⟨122327044546, 122327044550⟩, ⟨117325616349, 127415058897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 112721920 114032640 172359680 175308800 ⟨⟨125306884673, 125306884684⟩, ⟨120254043007, 130447198309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 112721920 114032640 175308800 178257920 ⟨⟨127160950655, 127160950665⟩, ⟨122098004029, 132311081947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 114032640 115343360 172359680 175308800 ⟨⟨124175370587, 124175370591⟩, ⟨119163706245, 129273345599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 114032640 115343360 175308800 178257920 ⟨⟨126016710592, 126016710597⟩, ⟨120994912199, 131124544068⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 115343360 166461440 178257920 t = true :=
  ⟨_, (join_su (m := 112721920) (by decide) (join_sr (m := 172359680) (by decide) (join_su (m := 111411200) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 169410560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 111411200) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 175308800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 172359680) (by decide) (join_su (m := 114032640) (by decide) (join_sr (m := 169410560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 169410560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 114032640) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 175308800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (127/640 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
