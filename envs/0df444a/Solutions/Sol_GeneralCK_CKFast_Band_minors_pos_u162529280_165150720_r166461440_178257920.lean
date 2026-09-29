-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_165150720_r166461440_178257920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:47:41.420874+00:00
-- url     : https://prove2.me/submissions/da943b09-9c28-4c73-8ea0-4da79ce27b63

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 63/320]`, `ρ ∈ [127/640, 17/80]` by 13 cells of the computing
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
theorem cell0 : cellOK 162529280 163184640 166461440 169410560 ⟨⟨87617937937, 87617937945⟩, ⟨85223151256, 90034726969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 163184640 163840000 166461440 169410560 ⟨⟨87251223847, 87251223855⟩, ⟨84864499604, 89659829596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 163184640 169410560 172359680 ⟨⟨89046692252, 89046692258⟩, ⟨86646469903, 91468889113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163184640 163840000 169410560 172359680 ⟨⟨88674801385, 88674801392⟩, ⟨86282651795, 91088805362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 163840000 164495360 166461440 169410560 ⟨⟨86886173954, 86886173962⟩, ⟨84507460438, 89286649173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 164495360 165150720 166461440 169410560 ⟨⟨86522773181, 86522773189⟩, ⟨84152019206, 88915170098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163840000 164495360 169410560 172359680 ⟨⟨88304589533, 88304589541⟩, ⟨85920461083, 90710453277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 164495360 165150720 169410560 172359680 ⟨⟨87936041539, 87936041547⟩, ⟨85559883132, 90333817178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 163840000 172359680 175308800 ⟨⟨90283490610, 90283490619⟩, ⟨86410016907, 94213550240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 162529280 163840000 175308800 178257920 ⟨⟨91703260448, 91703260455⟩, ⟨87820119931, 95642947931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 163840000 164495360 172359680 175308800 ⟨⟨89719847185, 89719847192⟩, ⟨87330329586, 92131073500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 164495360 165150720 172359680 175308800 ⟨⟨89346185884, 89346185891⟩, ⟨86964648468, 91749314649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163840000 165150720 175308800 178257920 ⟨⟨90942389902, 90942389911⟩, ⟨87082329721, 94858449708⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 165150720 166461440 178257920 t = true :=
  ⟨_, (join_sr (m := 172359680) (by decide) (join_su (m := 163840000) (by decide) (join_sr (m := 169410560) (by decide) (join_su (m := 163184640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 163184640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 169410560) (by decide) (join_su (m := 164495360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 164495360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 163840000) (by decide) (join_sr (m := 175308800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 175308800) (by decide) (join_su (m := 164495360) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (127/640 : ℝ) (17/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  have e3 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
