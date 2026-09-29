-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r187105280_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:03:59.82769+00:00
-- url     : https://prove2.me/submissions/c76f2917-22e8-4a17-9b79-467cd0cd4543

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [571/2560, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 187105280 188497920 ⟨⟨57277862712, 57277862713⟩, ⟨55842428171, 58721797961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 243793920 244449280 188497920 189890560 ⟨⟨57690139802, 57690139804⟩, ⟨56253000872, 59135785121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 244449280 245104640 187105280 188497920 ⟨⟨57014229523, 57014229528⟩, ⟨55581706236, 58455226808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 188497920 189890560 ⟨⟨57424716575, 57424716582⟩, ⟨55990493235, 58867419620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 244449280 189890560 191283200 ⟨⟨58102252046, 58102252049⟩, ⟨56663409006, 59549607144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243793920 244449280 191283200 192675840 ⟨⟨58514199826, 58514199828⟩, ⟨57073652955, 59963264416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 245104640 189890560 191283200 ⟨⟨57835040904, 57835040909⟩, ⟨56399117775, 59279449432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244449280 245104640 191283200 192675840 ⟨⟨58245202883, 58245202889⟩, ⟨56807580234, 59691316621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245760000 187105280 188497920 ⟨⟨56751257426, 56751257431⟩, ⟨55321631963, 58189330336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245104640 245760000 188497920 189890560 ⟨⟨57159957547, 57159957553⟩, ⟨55728636364, 58599731913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245760000 246415360 187105280 188497920 ⟨⟨56488941621, 56488941626⟩, ⟨55062200650, 57924103655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245760000 246415360 188497920 189890560 ⟨⟨56895857903, 56895857908⟩, ⟨55467425537, 58332717090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 189890560 191283200 ⟨⟨57568497046, 57568497051⟩, ⟨56135480392, 59009972603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 245760000 191283200 192675840 ⟨⟨57976876289, 57976876295⟩, ⟨56542164421, 59420052777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246415360 189890560 191283200 ⟨⟨57302615639, 57302615645⟩, ⟨55872492118, 58741171730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 191283200 192675840 ⟨⟨57709215193, 57709215200⟩, ⟨56277400760, 59149467941⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 187105280 192675840 t = true :=
  ⟨_, (join_su (m := 245104640) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 188497920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 244449280) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 191283200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 189890560) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 188497920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245760000) (by decide) (join_sr (m := 191283200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 191283200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (571/2560 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
