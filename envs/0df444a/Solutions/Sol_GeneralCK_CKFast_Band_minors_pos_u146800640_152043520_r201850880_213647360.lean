-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_152043520_r201850880_213647360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:48:52.5011+00:00
-- url     : https://prove2.me/submissions/003ef1be-ab00-42a2-88c1-4e1641c7ced5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 29/160]`, `ρ ∈ [77/320, 163/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 148111360 201850880 204800000 ⟨⟨115146956451, 115146956455⟩, ⟨110873104671, 119483929527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 148111360 204800000 207749120 ⟨⟨116654280765, 116654280769⟩, ⟨112370915372, 121000675253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 148111360 149422080 201850880 204800000 ⟨⟨114200341563, 114200341572⟩, ⟨109953875182, 118509293650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 149422080 204800000 207749120 ⟨⟨115697570312, 115697570321⟩, ⟨111441602719, 120015936070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 148111360 207749120 210698240 ⟨⟨118157856393, 118157856397⟩, ⟨113865025639, 122513623482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 148111360 210698240 213647360 ⟨⟨119657714677, 119657714679⟩, ⟨115355466281, 124022806095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 148111360 149422080 207749120 210698240 ⟨⟨117191126209, 117191126217⟩, ⟨112925704465, 121518858015⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 148111360 149422080 210698240 213647360 ⟨⟨118681039702, 118681039709⟩, ⟨114406210354, 123018090455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 149422080 150732800 201850880 204800000 ⟨⟨113262641908, 113262641917⟩, ⟨109043184967, 117543960000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 149422080 150732800 204800000 207749120 ⟨⟨114749822253, 114749822262⟩, ⟨110520877738, 119040544897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 150732800 152043520 201850880 204800000 ⟨⟨112333693844, 112333693852⟩, ⟨108140878128, 116587756938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 150732800 152043520 204800000 207749120 ⟨⟨113810872695, 113810872704⟩, ⟨109608584221, 118074329904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 150732800 207749120 210698240 ⟨⟨116233404144, 116233404151⟩, ⟨111995017942, 120533484885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 149422080 150732800 210698240 213647360 ⟨⟨117713417159, 117713417166⟩, ⟨113465634669, 122022810043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 150732800 152043520 207749120 210698240 ⟨⟨115284526079, 115284526088⟩, ⟨111072809587, 119557332094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 150732800 152043520 210698240 213647360 ⟨⟨116754682733, 116754682740⟩, ⟨112533582490, 121036792726⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 152043520 201850880 213647360 t = true :=
  ⟨_, (join_su (m := 149422080) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 148111360) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 204800000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 148111360) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 210698240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 207749120) (by decide) (join_su (m := 150732800) (by decide) (join_sr (m := 204800000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 204800000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 150732800) (by decide) (join_sr (m := 210698240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 210698240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (163/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
