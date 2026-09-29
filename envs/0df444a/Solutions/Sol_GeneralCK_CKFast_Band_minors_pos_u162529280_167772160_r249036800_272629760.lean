-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_167772160_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:59:04.960234+00:00
-- url     : https://prove2.me/submissions/418ffef9-8318-48f6-82df-1ea3a9b1e385

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 1/5]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163840000 249036800 254935040 ⟨⟨126903080685, 126903080692⟩, ⟨121851963580, 132038589119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 163840000 165150720 249036800 254935040 ⟨⟨125903253168, 125903253177⟩, ⟨120884667424, 131005432868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 163840000 254935040 260833280 ⟨⟨129587786339, 129587786346⟩, ⟨124517545341, 134742164989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163840000 165150720 254935040 260833280 ⟨⟨128570752065, 128570752073⟩, ⟨123533059680, 133691795897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 166461440 249036800 254935040 ⟨⟨124911197391, 124911197400⟩, ⟨119924768407, 129980434629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 166461440 167772160 249036800 254935040 ⟨⟨123926786853, 123926786858⟩, ⟨118972146723, 128963460975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165150720 166461440 254935040 260833280 ⟨⟨127561542721, 127561542730⟩, ⟨122556026985, 132649635064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 166461440 167772160 254935040 260833280 ⟨⟨126560031771, 126560031775⟩, ⟨121586327318, 131615549127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 163840000 260833280 266731520 ⟨⟨132262228789, 132262228797⟩, ⟨127173019918, 137435319656⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 165150720 260833280 266731520 ⟨⟨131228189014, 131228189021⟩, ⟨126171542252, 136367942713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 162529280 163840000 266731520 272629760 ⟨⟨134926560404, 134926560413⟩, ⟨129818536639, 140118208568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 163840000 165150720 266731520 272629760 ⟨⟨133875712308, 133875712317⟩, ⟨128800260505, 139034024573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165150720 166461440 260833280 266731520 ⟨⟨130202023915, 130202023922⟩, ⟨125177569997, 135308820768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166461440 167772160 260833280 266731520 ⟨⟨129183606972, 129183606974⟩, ⟨124190983130, 134257820584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 166461440 266731520 272629760 ⟨⟨132832785296, 132832785304⟩, ⟨127789538940, 137958138929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166461440 167772160 266731520 272629760 ⟨⟨131797652914, 131797652919⟩, ⟨126786251889, 136890418573⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 167772160 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 163840000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 166461440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 165150720) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 163840000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 163840000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 266731520) (by decide) (join_su (m := 166461440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 166461440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
