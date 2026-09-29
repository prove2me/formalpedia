-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r111411200_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:26:45.743897+00:00
-- url     : https://prove2.me/submissions/20731848-3b85-462c-bbc8-9707d08658dd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 7/200]`, `ρ ∈ [17/128, 207/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 25165824 26214400 111411200 117473280 ⟨⟨211053728213, 211053728236⟩, ⟨195636658276, 227171888358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 26214400 27262976 111411200 117473280 ⟨⟨207580892113, 207580892136⟩, ⟨192493749355, 223345195560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 25165824 26214400 117473280 123535360 ⟨⟨218134239348, 218134239372⟩, ⟨202842746023, 234095316552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 26214400 27262976 117473280 123535360 ⟨⟨214634480032, 214634480056⟩, ⟨199662684567, 230253780277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 27262976 28311552 111411200 117473280 ⟨⟨204226798822, 204226798845⟩, ⟨189455464560, 219652600512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 28311552 29360128 111411200 117473280 ⟨⟨200984890516, 200984890538⟩, ⟨186516146534, 216086560879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 27262976 28311552 117473280 123535360 ⟨⟨211251361474, 211251361496⟩, ⟨196585905282, 226543343946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 28311552 29360128 117473280 123535360 ⟨⟨207978573509, 207978573527⟩, ⟨193606932790, 222956790584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 25165824 26214400 123535360 129597440 ⟨⟨225004602879, 225004602899⟩, ⟨209838432344, 240810757934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 26214400 27262976 123535360 129597440 ⟨⟨221482270829, 221482270848⟩, ⟨206625964801, 236958170513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 25165824 26214400 129597440 135659520 ⟨⟨231678706190, 231678706214⟩, ⟨216637226038, 247332330785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 26214400 27262976 129597440 135659520 ⟨⟨228137630130, 228137630153⟩, ⟨213396568661, 243471987925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 27262976 28311552 123535360 129597440 ⟨⟨218074446911, 218074446928⟩, ⟨203515356018, 233233721185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 28311552 29360128 123535360 129597440 ⟨⟨214775057781, 214775057798⟩, ⟨200501307794, 229630499751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 27262976 28311552 129597440 135659520 ⟨⟨224708917348, 224708917367⟩, ⟨210256287082, 239736870018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 28311552 29360128 129597440 135659520 ⟨⟨221386720414, 221386720436⟩, ⟨207211254788, 236120355883⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 29360128 111411200 135659520 t = true :=
  ⟨_, (join_sr (m := 123535360) (by decide) (join_su (m := 27262976) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 26214400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 26214400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 117473280) (by decide) (join_su (m := 28311552) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 28311552) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 27262976) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 26214400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 26214400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 129597440) (by decide) (join_su (m := 28311552) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 28311552) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (7/200 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
