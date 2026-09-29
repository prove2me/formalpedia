-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r326369280_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:41:40.527136+00:00
-- url     : https://prove2.me/submissions/d1e2facc-b276-4777-ae0f-369cc269563c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [249/640, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 326369280 331939840 ⟨⟨126075337501, 126075337509⟩, ⟨121759975149, 130451748168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 205783040 207093760 326369280 331939840 ⟨⟨125076975805, 125076975810⟩, ⟨120784807087, 129429762806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 204472320 205783040 331939840 337510400 ⟨⟨128054472887, 128054472895⟩, ⟨123723290660, 132446675424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 331939840 337510400 ⟨⟨127042680046, 127042680051⟩, ⟨122734730138, 131411224615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 207093760 208404480 326369280 331939840 ⟨⟨124083814488, 124083814495⟩, ⟨119814637499, 128413184321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 208404480 209715200 326369280 331939840 ⟨⟨123095782957, 123095782964⟩, ⟨118849398584, 127401939256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207093760 208404480 331939840 337510400 ⟨⟨126036109206, 126036109214⟩, ⟨121751190802, 130381201110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 208404480 209715200 331939840 337510400 ⟨⟨125034689803, 125034689810⟩, ⟨120772604844, 129356531512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 205783040 337510400 343080960 ⟨⟨130029581708, 130029581714⟩, ⟨125682624954, 134437529327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205783040 207093760 337510400 343080960 ⟨⟨129004441398, 129004441403⟩, ⟨124680754186, 133388698228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 204472320 205783040 343080960 348651520 ⟨⟨132000710204, 132000710211⟩, ⟨127638023665, 136424356729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 205783040 207093760 343080960 348651520 ⟨⟨130962304894, 130962304900⟩, ⟨126622923679, 135362229263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 207093760 208404480 337510400 343080960 ⟨⟨127984543350, 127984543358⟩, ⟨123683925977, 132345313471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 208404480 209715200 337510400 343080960 ⟨⟨126969817041, 126969817049⟩, ⟨122692072530, 131307301738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 208404480 343080960 348651520 ⟨⟨129929160772, 129929160778⟩, ⟨125612886315, 134305565819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 208404480 209715200 343080960 348651520 ⟨⟨128901207371, 128901207379⟩, ⟨124607843802, 133254293177⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 326369280 348651520 t = true :=
  ⟨_, (join_sr (m := 337510400) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 205783040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 331939840) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 208404480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 207093760) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 205783040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 343080960) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 208404480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
