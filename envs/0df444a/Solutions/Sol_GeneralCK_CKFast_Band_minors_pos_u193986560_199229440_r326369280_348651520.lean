-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r326369280_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:41:08.893682+00:00
-- url     : https://prove2.me/submissions/fb09d683-df24-4595-ae94-b6789a25a8c5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [249/640, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 326369280 331939840 ⟨⟨134258299695, 134258299703⟩, ⟨129749765651, 138831495800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 195297280 196608000 326369280 331939840 ⟨⟨133215652971, 133215652980⟩, ⟨128732035167, 137763463578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 195297280 331939840 337510400 ⟨⟨136345657038, 136345657046⟩, ⟨131821037292, 140934871579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 331939840 337510400 ⟨⟨135289408055, 135289408064⟩, ⟨130789733167, 139853213821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 196608000 197918720 326369280 331939840 ⟨⟨132178814115, 132178814123⟩, ⟨127719886261, 136701470669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 197918720 199229440 326369280 331939840 ⟨⟨131147702784, 131147702790⟩, ⟨126713241843, 135645433409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 196608000 197918720 331939840 337510400 ⟨⟨134238988065, 134238988073⟩, ⟨129764033146, 138777614974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 197918720 199229440 331939840 337510400 ⟨⟨133194316820, 133194316827⟩, ⟨128743860189, 137707991510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 195297280 337510400 343080960 ⟨⟨138428267093, 138428267101⟩, ⟨133887619587, 143033440572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 195297280 196608000 337510400 343080960 ⟨⟨137358511106, 137358511114⟩, ⟨132842835415, 141938254209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 193986560 195297280 343080960 348651520 ⟨⟨140506186885, 140506186892⟩, ⟨135949568740, 145127260631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 195297280 196608000 343080960 348651520 ⟨⟨139423017685, 139423017693⟩, ⟨134891396679, 144018641097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 337510400 343080960 ⟨⟨136294603722, 136294603731⟩, ⟨131803676382, 140849144812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 197918720 199229440 337510400 343080960 ⟨⟨135236464810, 135236464818⟩, ⟨130770065521, 139766029017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 197918720 343080960 348651520 ⟨⟨138345715223, 138345715229⟩, ⟨133838869339, 142916115087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 197918720 199229440 343080960 348651520 ⟨⟨137274199492, 137274199501⟩, ⟨132791909842, 141819599407⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 326369280 348651520 t = true :=
  ⟨_, (join_sr (m := 337510400) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 195297280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 331939840) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 197918720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 196608000) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 195297280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 343080960) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 197918720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
