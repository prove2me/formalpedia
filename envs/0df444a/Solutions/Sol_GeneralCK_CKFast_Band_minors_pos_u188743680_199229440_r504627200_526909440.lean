-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r504627200_526909440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:54:12.783685+00:00
-- url     : https://prove2.me/submissions/10c71c79-fd20-4468-89dc-ca734c796552

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [77/128, 201/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 504627200 510197760 ⟨⟨204039575738, 204039575744⟩, ⟨195457541177, 212799155806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 191365120 510197760 515768320 ⟨⟨206039656012, 206039656018⟩, ⟨197430104707, 214826499464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 193986560 504627200 510197760 ⟨⟨201129013628, 201129013637⟩, ⟨192621859348, 209812380752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 510197760 515768320 ⟨⟨203106815797, 203106815806⟩, ⟨194572100139, 211817521953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 191365120 515768320 521338880 ⟨⟨208036350038, 208036350040⟩, ⟨199399342746, 216850390903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 191365120 521338880 526909440 ⟨⟨210029703047, 210029703053⟩, ⟨201365299599, 218870876291⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 193986560 515768320 521338880 ⟨⟨205081351444, 205081351452⟩, ⟨196519131910, 213819333968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 191365120 193986560 521338880 526909440 ⟨⟨207052663848, 207052663857⟩, ⟨198462997067, 215817860954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 196608000 504627200 510197760 ⟨⟨198242691993, 198242692002⟩, ⟨189809352766, 206850924239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 193986560 196608000 510197760 515768320 ⟨⟨200198157318, 200198157327⟩, ⟨191737224196, 208833791059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 199229440 504627200 510197760 ⟨⟨195380029055, 195380029064⟩, ⟨187019464249, 203914179912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 196608000 199229440 510197760 515768320 ⟨⟨197313102461, 197313102470⟩, ⟨188924922901, 205874704590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 515768320 521338880 ⟨⟨202150472928, 202150472938⟩, ⟨193662000204, 210813448774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193986560 196608000 521338880 526909440 ⟨⟨204099680218, 204099680228⟩, ⟨195583721361, 212789939602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 199229440 515768320 521338880 ⟨⟨199243140071, 199243140080⟩, ⟨190827396885, 207832137317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 521338880 526909440 ⟨⟨201170181465, 201170181474⟩, ⟨192726925007, 209786518445⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 504627200 526909440 t = true :=
  ⟨_, (join_su (m := 193986560) (by decide) (join_sr (m := 515768320) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 510197760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 510197760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 191365120) (by decide) (join_sr (m := 521338880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 521338880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 515768320) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 510197760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 510197760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 196608000) (by decide) (join_sr (m := 521338880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 521338880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (77/128 : ℝ) (201/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  have e3 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
