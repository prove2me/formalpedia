-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_20971520_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:18:12.37763+00:00
-- url     : https://prove2.me/submissions/0828bf95-2c8a-485f-8779-6dc97556ff10

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/40]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 17825792 75038720 78069760 ⟨⟨192178433335, 192178433365⟩, ⟨177382746878, 207717201773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 16777216 17825792 78069760 81100800 ⟨⟨196885892872, 196885892896⟩, ⟨182185573735, 212305203132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 17825792 18874368 75038720 78069760 ⟨⟨187562987033, 187562987062⟩, ⟨173236927635, 202593460017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 17825792 18874368 78069760 81100800 ⟨⟨192246026985, 192246027009⟩, ⟨178004750640, 207169736423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 16777216 17825792 81100800 84131840 ⟨⟨201480187677, 201480187707⟩, ⟨186874967364, 216781402858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 16777216 17825792 84131840 87162880 ⟨⟨205967033337, 205967033361⟩, ⟨191456490914, 221151605216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 17825792 18874368 81100800 84131840 ⟨⟨196819245858, 196819245888⟩, ⟨182662790331, 211637112381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 17825792 18874368 84131840 87162880 ⟨⟨201288049308, 201288049337⟩, ⟨187216295480, 216001097132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 18874368 19922944 75038720 78069760 ⟨⟨183183773840, 183183773868⟩, ⟨169297096787, 197739236024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 18874368 19922944 78069760 81100800 ⟨⟨187839386580, 187839386609⟩, ⟨174028056662, 202299398511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 19922944 20971520 75038720 78069760 ⟨⟨179021770113, 179021770135⟩, ⟨165547092468, 193132333745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 19922944 20971520 78069760 81100800 ⟨⟨183647470809, 183647470837⟩, ⟨170239706966, 197672692896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 18874368 19922944 81100800 84131840 ⟨⟨192388477570, 192388477592⟩, ⟨178652782595, 206753593031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 18874368 19922944 84131840 87162880 ⟨⟨196836159195, 196836159223⟩, ⟨183176228511, 211107045802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 19922944 20971520 81100800 84131840 ⟨⟨188169889041, 188169889069⟩, ⟨174829530338, 202110019350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 19922944 20971520 84131840 87162880 ⟨⟨192593860324, 192593860345⟩, ⟨179321240173, 206449269017⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 20971520 75038720 87162880 t = true :=
  ⟨_, (join_su (m := 18874368) (by decide) (join_sr (m := 81100800) (by decide) (join_su (m := 17825792) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 78069760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 17825792) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 84131840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 81100800) (by decide) (join_su (m := 19922944) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 78069760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 19922944) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 84131840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/40 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((20971520 : ℤ) : ℝ) / (D : ℝ)) = (1/40 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
