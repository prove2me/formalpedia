-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:22:52.220547+00:00
-- url     : https://prove2.me/submissions/4fb8be23-bc6f-41bc-aab1-c22822f971c6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 7/200]`, `ρ ∈ [303/2560, 17/128]` by 8 cells of the computing
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
theorem cell0 : cellOK 25165824 26214400 99287040 105349120 ⟨⟨196199389683, 196199389707⟩, ⟨180532376547, 212636892473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 26214400 27262976 99287040 105349120 ⟨⟨192795955907, 192795955931⟩, ⟨177480532819, 208853673550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 25165824 26214400 105349120 111411200 ⟨⟨203747756404, 203747756428⟩, ⟨188205322235, 220024856494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 26214400 27262976 105349120 111411200 ⟨⟨200306796289, 200306796312⟩, ⟨185104919805, 216217377660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 27262976 28311552 99287040 105349120 ⟨⟨189515278886, 189515278904⟩, ⟨174535639478, 205210582043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 28311552 29360128 99287040 105349120 ⟨⟨186350274550, 186350274568⟩, ⟨171691665194, 201699366637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 27262976 28311552 105349120 111411200 ⟨⟨196986627347, 196986627370⟩, ⟨182110375185, 212547013271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 28311552 29360128 105349120 111411200 ⟨⟨193780433566, 193780433588⟩, ⟨179215845234, 209005876355⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 29360128 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 27262976) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 26214400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 26214400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 105349120) (by decide) (join_su (m := 28311552) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 28311552) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (7/200 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
