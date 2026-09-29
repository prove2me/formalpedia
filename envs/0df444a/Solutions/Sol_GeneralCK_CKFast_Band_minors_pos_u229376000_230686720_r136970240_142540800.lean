-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u229376000_230686720_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:59:52.714141+00:00
-- url     : https://prove2.me/submissions/dd3f66cf-d40d-47e4-8c8b-44de6141dfa8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [35/128, 11/40]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 229376000 229703680 136970240 138362880 ⟨⟨46869164691, 46869164696⟩, ⟨46018138733, 47723426875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 229703680 230031360 136970240 138362880 ⟨⟨46763726878, 46763726883⟩, ⟨45913793225, 47616889938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 229376000 229703680 138362880 139755520 ⟨⟨47330336897, 47330336903⟩, ⟨46478315439, 48185595760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 229703680 230031360 138362880 139755520 ⟨⟨47223915719, 47223915724⟩, ⟨46372988110, 48078073918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230031360 230359040 136970240 138362880 ⟨⟨46658447798, 46658447800⟩, ⟨45809603876, 47510514328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230359040 230686720 136970240 138362880 ⟨⟨46553326837, 46553326844⟩, ⟨45705570080, 47404299433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 230031360 230359040 138362880 139755520 ⟨⟨47117654419, 47117654420⟩, ⟨46267818083, 47970714551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230359040 230686720 138362880 139755520 ⟨⟨47011552379, 47011552385⟩, ⟨46162804750, 47863517043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 229376000 229703680 139755520 141148160 ⟨⟨47791270616, 47791270621⟩, ⟨46938254178, 48647525625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 229703680 230031360 139755520 141148160 ⟨⟨47683867563, 47683867569⟩, ⟨46831946516, 48539020380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 229703680 141148160 142540800 ⟨⟨48251966431, 48251966438⟩, ⟨47397955539, 49109217063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229703680 230031360 141148160 142540800 ⟨⟨48143582996, 48143583003⟩, ⟨47290669025, 48999729911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 230031360 230359040 139755520 141148160 ⟨⟨47576625529, 47576625532⟩, ⟨46725797292, 48430678750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 230359040 230686720 139755520 141148160 ⟨⟨47469543889, 47469543896⟩, ⟨46619805893, 48322500116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 230031360 230359040 141148160 142540800 ⟨⟨48035361710, 48035361712⟩, ⟨47183542078, 48890407506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230359040 230686720 141148160 142540800 ⟨⟨47927301944, 47927301950⟩, ⟨47076574082, 48781249223⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 229376000 230686720 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 230031360) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 229703680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 229703680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 230359040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 230359040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 230031360) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 229703680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 229703680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 230359040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 230359040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (35/128 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((229376000 : ℤ) : ℝ) / (D : ℝ)) = (35/128 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
