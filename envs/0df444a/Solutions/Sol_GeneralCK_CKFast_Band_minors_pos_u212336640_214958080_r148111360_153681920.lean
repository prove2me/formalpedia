-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_214958080_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:26:15.467394+00:00
-- url     : https://prove2.me/submissions/f22d9a33-c671-453c-bd70-c22b5d33b8fc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 41/160]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 212336640 212992000 148111360 149504000 ⟨⟨56628003544, 56628003551⟩, ⟨55089095732, 58176807883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212336640 212992000 149504000 150896640 ⟨⟨57138869916, 57138869922⟩, ⟨55598011895, 58689628674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212992000 213647360 148111360 149504000 ⟨⟨56382538965, 56382538970⟩, ⟨54847182372, 57927753995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212992000 213647360 149504000 150896640 ⟨⟨56891342131, 56891342137⟩, ⟨55354040489, 58438506474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 212992000 150896640 152289280 ⟨⟨57649416235, 57649416242⟩, ⟨56106609271, 59202128129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 212336640 212992000 152289280 153681920 ⟨⟨58159643370, 58159643376⟩, ⟨56614888726, 59714307116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212992000 213647360 150896640 152289280 ⟨⟨57399829039, 57399829045⟩, ⟨55860583588, 58948941435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212992000 213647360 152289280 153681920 ⟨⟨57908000542, 57908000548⟩, ⟨56366812519, 59459059738⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 213647360 214302720 148111360 149504000 ⟨⟨56137890173, 56137890178⟩, ⟨54606065717, 57679535255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 213647360 214302720 149504000 150896640 ⟨⟨56644635215, 56644635220⟩, ⟨55110870861, 58188224508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214302720 214958080 148111360 149504000 ⟨⟨55894050759, 55894050763⟩, ⟨54365739509, 57432145095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 214302720 214958080 149504000 150896640 ⟨⟨56398742728, 56398742732⟩, ⟨54868496724, 57938776179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213647360 214302720 150896640 152289280 ⟨⟨57151067754, 57151067760⟩, ⟨55615364717, 58696600027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 213647360 214302720 152289280 153681920 ⟨⟨57657188631, 57657188636⟩, ⟨56119548121, 59204662655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 214302720 214958080 150896640 152289280 ⟨⟨56903125910, 56903125914⟩, ⟨55370946341, 58445097274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214302720 214958080 152289280 153681920 ⟨⟨57407201134, 57407201136⟩, ⟨55873089182, 58951109208⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 214958080 148111360 153681920 t = true :=
  ⟨_, (join_su (m := 213647360) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 212992000) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 149504000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212992000) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 152289280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 150896640) (by decide) (join_su (m := 214302720) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 149504000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 214302720) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 152289280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
