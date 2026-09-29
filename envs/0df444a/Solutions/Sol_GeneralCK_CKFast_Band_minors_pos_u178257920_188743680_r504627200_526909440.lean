-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r504627200_526909440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:22.06833+00:00
-- url     : https://prove2.me/submissions/39925afb-47c3-42a6-ac68-1c2493bcbe89

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [77/128, 201/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 504627200 510197760 ⟨⟨215936459021, 215936459029⟩, ⟨207043731032, 225012190482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 180879360 510197760 515768320 ⟨⟨218024984191, 218024984199⟩, ⟨209105049180, 227127533926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 183500800 504627200 510197760 ⟨⟨212922775323, 212922775332⟩, ⟨204109450641, 221917720046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 510197760 515768320 ⟨⟨214989297929, 214989297937⟩, ⟨206148668063, 224011194709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 180879360 515768320 521338880 ⟨⟨220109614441, 220109614449⟩, ⟨211162546526, 229238903014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 180879360 521338880 526909440 ⟨⟨222190403582, 222190403592⟩, ⟨213216275706, 231346352736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 183500800 515768320 521338880 ⟨⟨217052057298, 217052057308⟩, ⟨208184192987, 226100830091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180879360 183500800 521338880 526909440 ⟨⟨219111104983, 219111104992⟩, ⟨210216075853, 228186678857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 186122240 504627200 510197760 ⟨⟨209935831989, 209935831998⟩, ⟨201200738843, 218851174308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 183500800 186122240 510197760 515768320 ⟨⟨211980276639, 211980276647⟩, ⟨203217794333, 220922689407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 188743680 504627200 510197760 ⟨⟨206974976658, 206974976667⟩, ⟨198316971205, 215811873082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186122240 188743680 510197760 515768320 ⟨⟨208997272443, 208997272452⟩, ⟨200311807486, 217861342904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 515768320 521338880 ⟨⟨214021086709, 214021086718⟩, ⟨205231282622, 222990497262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 183500800 186122240 521338880 526909440 ⟨⟨216058311571, 216058311580⟩, ⟨207241252034, 225054648289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 188743680 515768320 521338880 ⟨⟨211016059302, 211016059310⟩, ⟨202303198892, 219907234496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 521338880 526909440 ⟨⟨213031384500, 213031384510⟩, ⟨204291191699, 221949596108⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 504627200 526909440 t = true :=
  ⟨_, (join_su (m := 183500800) (by decide) (join_sr (m := 515768320) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 510197760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 510197760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 180879360) (by decide) (join_sr (m := 521338880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 521338880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 515768320) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 510197760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 510197760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 186122240) (by decide) (join_sr (m := 521338880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 521338880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (77/128 : ℝ) (201/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  have e3 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
