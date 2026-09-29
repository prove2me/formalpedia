-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:29:22.547867+00:00
-- url     : https://prove2.me/submissions/d01c3f72-9ef3-4156-ac03-1c084b496bb6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [43/128, 447/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 281804800 284590080 ⟨⟨83635110048, 83635110053⟩, ⟨81855030192, 85427378644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247070720 247726080 281804800 284590080 ⟨⟨83256745383, 83256745388⟩, ⟨81481047097, 85044591455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247070720 284590080 287375360 ⟨⟨84425401427, 84425401432⟩, ⟨82641745253, 86221255777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247070720 247726080 284590080 287375360 ⟨⟨84043736980, 84043736984⟩, ⟨82264470746, 85835160545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247726080 248381440 281804800 284590080 ⟨⟨82879186123, 82879186128⟩, ⟨81107852276, 84662627016⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248381440 249036800 281804800 284590080 ⟨⟨82502426789, 82502426796⟩, ⟨80735440363, 84281479734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 248381440 284590080 287375360 ⟨⟨83662881457, 83662881463⟩, ⟨81887988048, 85449891569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248381440 249036800 284590080 287375360 ⟨⟨83282829369, 83282829375⟩, ⟨81512291779, 85065443241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247070720 287375360 290160640 ⟨⟨85215160616, 85215160623⟩, ⟨83427929553, 87014599247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247070720 247726080 287375360 290160640 ⟨⟨84830203078, 84830203080⟩, ⟨83047370269, 86625202715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247070720 290160640 292945920 ⟨⟨86004390154, 86004390161⟩, ⟨84213585615, 87807411597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247070720 247726080 290160640 292945920 ⟨⟨85616146171, 85616146175⟩, ⟨83829748153, 87414720471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247726080 248381440 287375360 290160640 ⟨⟨84446057916, 84446057923⟩, ⟨82667606265, 86236635879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248381440 249036800 287375360 290160640 ⟨⟨84062719633, 84062719640⟩, ⟨82288632146, 85848893120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247726080 248381440 290160640 292945920 ⟨⟨85228717960, 85228717967⟩, ⟨83446709377, 87022862416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248381440 249036800 290160640 292945920 ⟨⟨84842100006, 84842100012⟩, ⟨83064463879, 86631831800⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 281804800 292945920 t = true :=
  ⟨_, (join_sr (m := 287375360) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 284590080) (by decide) (join_su (m := 247070720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 247070720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 284590080) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 248381440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 247726080) (by decide) (join_sr (m := 290160640) (by decide) (join_su (m := 247070720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 247070720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290160640) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 248381440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
