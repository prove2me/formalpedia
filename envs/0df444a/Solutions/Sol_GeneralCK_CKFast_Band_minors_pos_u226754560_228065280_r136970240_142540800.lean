-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u226754560_228065280_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:57:19.839491+00:00
-- url     : https://prove2.me/submissions/d26febfa-3094-4152-937e-cca1ca82b57f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [173/640, 87/320]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 226754560 227082240 136970240 138362880 ⟨⟨47718455620, 47718455624⟩, ⟨46858597247, 48581605632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 227082240 227409920 136970240 138362880 ⟨⟨47611725670, 47611725675⟩, ⟨46752980577, 48473755390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226754560 227082240 138362880 139755520 ⟨⟨48187536465, 48187536467⟩, ⟨47326670166, 49051695513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 227082240 227409920 138362880 139755520 ⟨⟨48079813844, 48079813849⟩, ⟨47220062386, 48942851051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 227409920 227737600 136970240 138362880 ⟨⟨47505159428, 47505159434⟩, ⟨46647524962, 48366071538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 227737600 228065280 136970240 138362880 ⟨⟨47398756265, 47398756271⟩, ⟨46542229776, 48258553435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 227409920 227737600 138362880 139755520 ⟨⟨47972256110, 47972256115⟩, ⟨47113616837, 48834174155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227737600 228065280 138362880 139755520 ⟨⟨47864862625, 47864862631⟩, ⟨47007332884, 48725664185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 226754560 227082240 139755520 141148160 ⟨⟨48656366576, 48656366580⟩, ⟨47794492930, 49521534082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 227082240 227409920 139755520 141148160 ⟨⟨48547652845, 48547652851⟩, ⟨47686895593, 49411696965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 226754560 227082240 141148160 142540800 ⟨⟨49124946585, 49124946589⟩, ⟨48262066165, 49991121968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 227082240 227409920 141148160 142540800 ⟨⟨49015243297, 49015243302⟩, ⟨48153480816, 49880293757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 227409920 227737600 139755520 141148160 ⟨⟨48439105169, 48439105174⟩, ⟨47579461651, 49302028584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 227737600 228065280 139755520 141148160 ⟨⟨48330722906, 48330722911⟩, ⟨47472190470, 49192528294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 227409920 227737600 141148160 142540800 ⟨⟨48905707223, 48905707228⟩, ⟨48045060021, 49769635442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227737600 228065280 141148160 142540800 ⟨⟨48796337718, 48796337724⟩, ⟨47936803141, 49659146375⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 226754560 228065280 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 227409920) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 227082240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 227082240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 227737600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 227737600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 227409920) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 227082240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 227082240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 227737600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 227737600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (173/640 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((226754560 : ℤ) : ℝ) / (D : ℝ)) = (173/640 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
