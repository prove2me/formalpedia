-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r415498240_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:10.409417+00:00
-- url     : https://prove2.me/submissions/808dfa71-8698-460d-9137-837335e72a54

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [317/640, 167/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 415498240 421068800 ⟨⟨181944253739, 181944253748⟩, ⟨173497936393, 190579065724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 180879360 421068800 426639360 ⟨⟨184102881876, 184102881885⟩, ⟨175627999147, 192765956654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 183500800 415498240 421068800 ⟨⟨179302504947, 179302504957⟩, ⟨170936643232, 187854909987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 421068800 426639360 ⟨⟨181436686165, 181436686174⟩, ⟨173042224993, 190017423394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 180879360 426639360 432209920 ⟨⟨186256674694, 186256674703⟩, ⟨177753321660, 194947911709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 180879360 432209920 437780480 ⟨⟨188405695774, 188405695783⟩, ⟨179873966073, 197124995927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 183500800 426639360 432209920 ⟨⟨183566205043, 183566205053⟩, ⟨175143234874, 192175178553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180879360 183500800 432209920 437780480 ⟨⟨185691122270, 185691122278⟩, ⟨177239732211, 194328237518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 186122240 415498240 421068800 ⟨⟨176688217790, 176688217799⟩, ⟨168401418770, 185159642493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 183500800 186122240 421068800 426639360 ⟨⟨178797937724, 178797937733⟩, ⟨170482518541, 187297749228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 188743680 415498240 421068800 ⟨⟨174100673842, 174100673851⟩, ⟨165891581973, 182492506758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186122240 188743680 421068800 426639360 ⟨⟨176185921815, 176185921823⟩, ⟨167948201816, 184606182042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 426639360 432209920 ⟨⟨180903163700, 180903163709⟩, ⟨172559210272, 189431270678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 183500800 186122240 432209920 437780480 ⟨⟨183003953622, 183003953630⟩, ⟨174631550605, 191560266029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 188743680 426639360 432209920 ⟨⟨178266839681, 178266839690⟩, ⟨170000573018, 186715440406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 432209920 437780480 ⟨⟨180343482683, 180343482692⟩, ⟨172048749633, 188820338286⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 415498240 437780480 t = true :=
  ⟨_, (join_su (m := 183500800) (by decide) (join_sr (m := 426639360) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 421068800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 421068800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 180879360) (by decide) (join_sr (m := 432209920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 432209920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 426639360) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 421068800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 421068800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 186122240) (by decide) (join_sr (m := 432209920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 432209920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (317/640 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
