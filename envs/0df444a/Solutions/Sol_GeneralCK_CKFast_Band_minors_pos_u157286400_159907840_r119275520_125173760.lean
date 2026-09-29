-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_159907840_r119275520_125173760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:29:37.893578+00:00
-- url     : https://prove2.me/submissions/e3551b7f-a11a-435a-9bff-a85da544baae

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 61/320]`, `ρ ∈ [91/640, 191/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 157941760 119275520 120750080 ⟨⟨66196429524, 66196429531⟩, ⟨64295129809, 68112703235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 157941760 120750080 122224640 ⟨⟨66962947378, 66962947386⟩, ⟨65058974055, 68881889607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157941760 158597120 119275520 120750080 ⟨⟨65907577106, 65907577113⟩, ⟨64012235358, 67817810184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 157941760 158597120 120750080 122224640 ⟨⟨66671103165, 66671103173⟩, ⟨64773094899, 68583997893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 157941760 122224640 123699200 ⟨⟨67728457930, 67728457938⟩, ⟨65821817681, 69650061947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 157941760 123699200 125173760 ⟨⟨68492965324, 68492965332⟩, ⟨66583664791, 70417224440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 157941760 158597120 122224640 123699200 ⟨⟨67433633295, 67433633303⟩, ⟨65532965088, 69349183045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 157941760 158597120 123699200 125173760 ⟨⟨68195171570, 68195171576⟩, ⟨66291849969, 70113369752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 158597120 159252480 119275520 120750080 ⟨⟨65620205498, 65620205500⟩, ⟨63730779023, 67524441427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 158597120 159252480 120750080 122224640 ⟨⟨66380751160, 66380751163⟩, ⟨64488665258, 68287641863⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 159252480 159907840 119275520 120750080 ⟨⟨65334300104, 65334300110⟩, ⟨63450746677, 67232581900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 159252480 159907840 120750080 122224640 ⟨⟨66091876681, 66091876688⟩, ⟨64205670923, 67992806370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 158597120 159252480 122224640 123699200 ⟨⟨67140312134, 67140312137⟩, ⟨65245573286, 69049851085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 158597120 159252480 123699200 125173760 ⟨⟨67898892434, 67898892438⟩, ⟨66001507085, 69811073138⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 159252480 159907840 122224640 123699200 ⟨⟨66848479689, 66848479695⟩, ⟨64959627981, 68752050841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 159252480 159907840 123699200 125173760 ⟨⟨67604113075, 67604113082⟩, ⟨65712621767, 69510319296⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 159907840 119275520 125173760 t = true :=
  ⟨_, (join_su (m := 158597120) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 157941760) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 120750080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 157941760) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 123699200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 122224640) (by decide) (join_su (m := 159252480) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 120750080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 159252480) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 123699200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (61/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (191/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
