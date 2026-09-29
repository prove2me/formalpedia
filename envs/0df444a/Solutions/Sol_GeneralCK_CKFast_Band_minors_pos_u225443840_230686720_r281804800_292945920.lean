-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:56:56.997944+00:00
-- url     : https://prove2.me/submissions/8a410d12-4db0-4ca3-975b-9857d2cca8a7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [43/128, 447/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 281804800 284590080 ⟨⟨95999157080, 95999157084⟩, ⟨92719558139, 99317148109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 225443840 226754560 284590080 287375360 ⟨⟨96895273816, 96895273819⟩, ⟨93608564822, 100220405111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226754560 228065280 281804800 284590080 ⟨⟨95186611706, 95186611713⟩, ⟨91921254991, 98490132586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 284590080 287375360 ⟨⟨96075896783, 96075896790⟩, ⟨92803456152, 99386532644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 225443840 226754560 287375360 290160640 ⟨⟨97790611871, 97790611873⟩, ⟨94496797555, 101122878476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225443840 226754560 290160640 292945920 ⟨⟨98685175279, 98685175282⟩, ⟨95384260347, 102024572265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 228065280 287375360 290160640 ⟨⟨96964421056, 96964421064⟩, ⟨93684900994, 100282167191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 226754560 228065280 290160640 292945920 ⟨⟨97852188445, 97852188452⟩, ⟨94565593411, 101177040176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 229376000 281804800 284590080 ⟨⟨94378036638, 94378036645⟩, ⟨91126795372, 97667216714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228065280 229376000 284590080 287375360 ⟨⟨95260505814, 95260505820⟩, ⟨92002206946, 98556775383⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 230686720 281804800 284590080 ⟨⟨93573377510, 93573377515⟩, ⟨90336126645, 96848344360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229376000 230686720 284590080 287375360 ⟨⟨94449046436, 94449046444⟩, ⟨91204764457, 97731077099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 287375360 290160640 ⟨⟨96142231739, 96142231746⟩, ⟨92876879515, 99445586342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 228065280 229376000 290160640 292945920 ⟨⟨97023218222, 97023218228⟩, ⟨93750816861, 100333653423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230686720 287375360 290160640 ⟨⟨95323989349, 95323989356⟩, ⟨92072680264, 98613079605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 290160640 292945920 ⟨⟨96198209946, 96198209953⟩, ⟨92939877740, 99494355600⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 281804800 292945920 t = true :=
  ⟨_, (join_su (m := 228065280) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 284590080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 226754560) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 290160640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 287375360) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 284590080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 229376000) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 290160640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
