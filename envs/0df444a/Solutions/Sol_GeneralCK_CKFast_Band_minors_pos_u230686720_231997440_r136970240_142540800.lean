-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_231997440_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:24:13.119982+00:00
-- url     : https://prove2.me/submissions/c5da2398-f090-4540-9d1c-915f919b774e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 177/640]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231014400 136970240 138362880 ⟨⟨46448363393, 46448363399⟩, ⟨45601691245, 47298244628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231014400 231342080 136970240 138362880 ⟨⟨46343556859, 46343556864⟩, ⟨45497966772, 47192349305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231014400 138362880 139755520 ⟨⟨46905608995, 46905609000⟩, ⟨46057947514, 47756480767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231014400 231342080 138362880 139755520 ⟨⟨46799823655, 46799823660⟩, ⟨45953245774, 47649605108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 231342080 231669760 136970240 138362880 ⟨⟨46238906632, 46238906638⟩, ⟨45394396069, 47086612849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 231669760 231997440 136970240 138362880 ⟨⟨46134412116, 46134412119⟩, ⟨45290978552, 46981034651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231342080 231669760 138362880 139755520 ⟨⟨46694195755, 46694195760⟩, ⟨45848698932, 47542889450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231669760 231997440 138362880 139755520 ⟨⟨46588724693, 46588724694⟩, ⟨45744306402, 47436333178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231014400 139755520 141148160 ⟨⟨47362622036, 47362622042⟩, ⟨46513971721, 48214483844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231014400 231342080 139755520 141148160 ⟨⟨47255859354, 47255859361⟩, ⟨46408294170, 48106629319⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231014400 141148160 142540800 ⟨⟨47819403087, 47819403094⟩, ⟨46969764434, 48672254429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231014400 231342080 141148160 142540800 ⟨⟨47711664522, 47711664528⟩, ⟨46863112524, 48563422501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231342080 231669760 139755520 141148160 ⟨⟨47149255235, 47149255240⟩, ⟨46302772640, 47998935920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 231669760 231997440 139755520 141148160 ⟨⟨47042809074, 47042809076⟩, ⟨46197406539, 47891403028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 231342080 231669760 141148160 142540800 ⟨⟨47604085636, 47604085641⟩, ⟨46756617750, 48454752819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 231669760 231997440 141148160 142540800 ⟨⟨47496665818, 47496665821⟩, ⟨46650279515, 48346244757⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 231997440 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 231014400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231014400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 231669760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 231669760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 231342080) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 231014400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231014400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 231669760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 231669760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (177/640 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((231997440 : ℤ) : ℝ) / (D : ℝ)) = (177/640 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
