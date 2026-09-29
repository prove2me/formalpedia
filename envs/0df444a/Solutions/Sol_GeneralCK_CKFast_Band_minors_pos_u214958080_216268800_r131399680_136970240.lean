-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_216268800_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:18:58.112561+00:00
-- url     : https://prove2.me/submissions/c86ee778-c7c6-49a2-9940-84dde886a335

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 33/128]`, `ρ ∈ [401/2560, 209/1280]` by 10 cells of the computing
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
theorem cell0 : cellOK 214958080 215285760 131399680 132792320 ⟨⟨49649662695, 49649662702⟩, ⟨48752132806, 50550750548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 215285760 215613440 131399680 132792320 ⟨⟨49540762607, 49540762608⟩, ⟨48644442537, 50440632631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 215613440 132792320 134184960 ⟨⟨50101559219, 50101559224⟩, ⟨48598045758, 51614768831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 215613440 215941120 131399680 132792320 ⟨⟨49432045619, 49432045625⟩, ⟨48536932305, 50330700915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 215941120 216268800 131399680 132792320 ⟨⟨49323511010, 49323511017⟩, ⟨48429601401, 50220954655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 215613440 216268800 132792320 134184960 ⟨⟨49882037301, 49882037307⟩, ⟨48381941519, 51391791711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 214958080 215613440 134184960 135577600 ⟨⟨50607613673, 50607613678⟩, ⟨49102157606, 52122770491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214958080 215613440 135577600 136970240 ⟨⟨51113353917, 51113353924⟩, ⟨49605956443, 52630456728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 215613440 216268800 134184960 135577600 ⟨⟨50386007788, 50386007793⟩, ⟨48883974815, 51897704034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 215613440 216268800 135577600 136970240 ⟨⟨50889667848, 50889667855⟩, ⟨49385698858, 52403304743⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 216268800 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 215613440) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 215285760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 132792320) (by decide) (join_su (m := 215941120) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 215613440) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 135577600) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (33/128 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((216268800 : ℤ) : ℝ) / (D : ℝ)) = (33/128 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
