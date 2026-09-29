-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:19:38.100288+00:00
-- url     : https://prove2.me/submissions/6de28b02-4741-48d1-aa6f-317fe1c0b4d1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 270663680 273448960 ⟨⟨81936979534, 81936979537⟩, ⟨80153655156, 83732622202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244449280 245104640 270663680 273448960 ⟨⟨81568664045, 81568664051⟩, ⟨79789757067, 83359847031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244449280 273448960 276234240 ⟨⟨82742771028, 82742771030⟩, ⟨80955830298, 84542039229⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 273448960 276234240 ⟨⟨82371113324, 82371113330⟩, ⟨80588598536, 84165913417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245104640 245760000 270663680 273448960 ⟨⟨81201161275, 81201161281⟩, ⟨79426654059, 82987902440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245760000 246415360 270663680 273448960 ⟨⟨80834465653, 80834465658⟩, ⟨79064340678, 82616782742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245104640 245760000 273448960 276234240 ⟨⟨82000272187, 82000272193⟩, ⟨80222165714, 83790622019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245760000 246415360 273448960 276234240 ⟨⟨81630242028, 81630242034⟩, ⟨79856526362, 83416159332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244449280 276234240 279019520 ⟨⟨83547992060, 83547992063⟩, ⟨81757436668, 85350884056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244449280 245104640 276234240 279019520 ⟨⟨83172999256, 83172999261⟩, ⟨81386878289, 84971414775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244449280 279019520 281804800 ⟨⟨84352645364, 84352645366⟩, ⟨82558476989, 86159159424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244449280 245104640 279019520 281804800 ⟨⟨83974324530, 83974324535⟩, ⟨82184599006, 85776353803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 276234240 279019520 ⟨⟨82798826796, 82798826802⟩, ⟨81017122642, 84592783673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245760000 246415360 276234240 279019520 ⟨⟨82425469078, 82425469085⟩, ⟨80648164240, 84214985029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 245760000 279019520 281804800 ⟨⟨83596827753, 83596827758⟩, ⟨81811527482, 85394390057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 279019520 281804800 ⟨⟨83220149414, 83220149421⟩, ⟨81439256912, 85013262451⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 270663680 281804800 t = true :=
  ⟨_, (join_sr (m := 276234240) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 273448960) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244449280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 273448960) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245760000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 245104640) (by decide) (join_sr (m := 279019520) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244449280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 279019520) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245760000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
