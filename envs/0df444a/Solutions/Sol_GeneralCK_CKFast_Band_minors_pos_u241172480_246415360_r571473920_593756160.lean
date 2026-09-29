-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r571473920_593756160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:43:16.640492+00:00
-- url     : https://prove2.me/submissions/50727147-38f3-453f-a749-357d8a6ef859

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [109/160, 453/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 571473920 577044480 ⟨⟨169005033547, 169005033555⟩, ⟨164646703319, 173415731228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242483200 243793920 571473920 577044480 ⟨⟨167605472070, 167605472078⟩, ⟨163267493576, 171995607137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 242483200 577044480 582615040 ⟨⟨170540396151, 170540396159⟩, ⟨166168064564, 174965114992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 577044480 582615040 ⟨⟨169129760836, 169129760844⟩, ⟨164777809877, 173533891136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 245104640 571473920 577044480 ⟨⟨166209663380, 166209663388⟩, ⟨161891929940, 170579343099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245104640 246415360 571473920 577044480 ⟨⟨164817564320, 164817564323⟩, ⟨160519970195, 169166895009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243793920 245104640 577044480 582615040 ⟨⟨167722869111, 167722869119⟩, ⟨163391193096, 172106517080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245104640 246415360 577044480 582615040 ⟨⟨166319678038, 166319678042⟩, ⟨162008172210, 170682948958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 242483200 582615040 588185600 ⟨⟨172074440034, 172074440041⟩, ⟨167688113039, 176513173074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243793920 582615040 588185600 ⟨⟨170652760288, 170652760297⟩, ⟨166286842280, 175070879411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 242483200 588185600 593756160 ⟨⟨173607181734, 173607181742⟩, ⟨169206865131, 178059922161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242483200 243793920 588185600 593756160 ⟨⟨172174486553, 172174486561⟩, ⟨167794606767, 176606588231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 582615040 588185600 ⟨⟨169234814492, 169234814500⟩, ⟨164889200793, 173632424844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 246415360 582615040 588185600 ⟨⟨167820559928, 167820559932⟩, ⟨163495146771, 172197765746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243793920 245104640 588185600 593756160 ⟨⟨170745515242, 170745515251⟩, ⟨166385968613, 175157082247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 588185600 593756160 ⟨⟨169320225312, 169320225316⟩, ⟨164980909070, 173711360828⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 571473920 593756160 t = true :=
  ⟨_, (join_sr (m := 582615040) (by decide) (join_su (m := 243793920) (by decide) (join_sr (m := 577044480) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242483200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 577044480) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245104640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243793920) (by decide) (join_sr (m := 588185600) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 242483200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 588185600) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245104640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (453/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
