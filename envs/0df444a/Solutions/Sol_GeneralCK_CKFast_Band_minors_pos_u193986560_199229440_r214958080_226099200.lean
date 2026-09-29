-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:24:52.344771+00:00
-- url     : https://prove2.me/submissions/d3095195-ef9f-401a-94e2-bb78ea3957b8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 214958080 217743360 ⟨⟨90870793733, 90870793741⟩, ⟨87394050615, 94392143121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 193986560 195297280 217743360 220528640 ⟨⟨91969969319, 91969969327⟩, ⟨88485241164, 95499313702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 195297280 196608000 214958080 217743360 ⟨⟨90126652720, 90126652726⟩, ⟨86667222316, 93630349587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 217743360 220528640 ⟨⟨91217868599, 91217868607⟩, ⟨87750482754, 94729532326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 195297280 220528640 223313920 ⟨⟨93067623209, 93067623217⟩, ⟨89574924576, 96604947664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193986560 195297280 223313920 226099200 ⟨⟨94163764463, 94163764471⟩, ⟨90663109819, 97709054166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 196608000 220528640 223313920 ⟨⟨92307595678, 92307595685⟩, ⟨88832268467, 95827211830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195297280 196608000 223313920 226099200 ⟨⟨93395842759, 93395842766⟩, ⟨89912588166, 96923396999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197918720 214958080 217743360 ⟨⟨89387503102, 89387503109⟩, ⟨85945197757, 92873739844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 196608000 197918720 217743360 220528640 ⟨⟨90470789884, 90470789892⟩, ⟨87020558923, 93964965079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 197918720 199229440 214958080 217743360 ⟨⟨88653268361, 88653268367⟩, ⟨85227903482, 92122234223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 197918720 199229440 217743360 220528640 ⟨⟨89728656392, 89728656400⟩, ⟨86295395938, 93205532041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 220528640 223313920 ⟨⟨91552620152, 91552620159⟩, ⟨88094477174, 95054719846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 197918720 223313920 226099200 ⟨⟨92633002456, 92633002464⟩, ⟨89166960974, 96143012788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 199229440 220528640 223313920 ⟨⟨90802619595, 90802619601⟩, ⟨87361476700, 94287391551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 223313920 226099200 ⟨⟨91875166277, 91875166284⟩, ⟨88426153994, 95367821143⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 214958080 226099200 t = true :=
  ⟨_, (join_su (m := 196608000) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 217743360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 195297280) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 223313920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 217743360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 197918720) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 223313920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
