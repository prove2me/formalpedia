-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r526909440_549191680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:00:35.193682+00:00
-- url     : https://prove2.me/submissions/176bf373-c05b-4399-afc9-8386aa478704

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [201/320, 419/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 526909440 532480000 ⟨⟨212019759879, 212019759885⟩, ⟨203328019178, 220888001382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 191365120 532480000 538050560 ⟨⟨214006564969, 214006564975⟩, ⟨205287545008, 222901811523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 193986560 526909440 532480000 ⟨⟨209020795915, 209020795925⟩, ⟨200403737647, 217813146682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 532480000 538050560 ⟨⟨210985790179, 210985790188⟩, ⟨202341395325, 219805234542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 191365120 538050560 543621120 ⟨⟨215990162365, 215990162372⟩, ⟨207243920232, 224912351664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 191365120 543621120 549191680 ⟨⟨217970595733, 217970595736⟩, ⟨209197187620, 226919666358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 193986560 538050560 543621120 ⟨⟨212947688810, 212947688818⟩, ⟨204276011416, 221794167551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 191365120 193986560 543621120 549191680 ⟨⟨214906533615, 214906533625⟩, ⟨206207626890, 223779988358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 196608000 526909440 532480000 ⟨⟨206045820235, 206045820244⟩, ⟨197502427898, 214763305404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 193986560 196608000 532480000 538050560 ⟨⟨207988933674, 207988933684⟩, ⟨199418159702, 216733587678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 199229440 526909440 532480000 ⟨⟨203094265895, 203094265904⟩, ⟨194623545753, 211737887988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 196608000 199229440 532480000 538050560 ⟨⟨205015432288, 205015432297⟩, ⟨196517297292, 213686285630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 538050560 543621120 ⟨⟨209929060895, 209929060904⟩, ⟨201330956329, 218700827583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193986560 196608000 543621120 549191680 ⟨⟨211866241917, 211866241926⟩, ⟨203240857008, 220665065927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 199229440 538050560 543621120 ⟨⟨206933719255, 206933719265⟩, ⟨198408217480, 215631750729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 543621120 549191680 ⟨⟨208849165093, 208849165102⟩, ⟨200296343865, 217574322322⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 526909440 549191680 t = true :=
  ⟨_, (join_su (m := 193986560) (by decide) (join_sr (m := 538050560) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 532480000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 532480000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 191365120) (by decide) (join_sr (m := 543621120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 543621120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 538050560) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 532480000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 532480000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 196608000) (by decide) (join_sr (m := 543621120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 543621120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (201/320 : ℝ) (419/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  have e3 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
