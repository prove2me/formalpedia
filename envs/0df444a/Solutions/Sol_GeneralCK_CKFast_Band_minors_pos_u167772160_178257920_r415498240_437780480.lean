-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r415498240_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:44:57.111119+00:00
-- url     : https://prove2.me/submissions/8ffbac72-3666-41f1-86b2-808bcf8464a3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [317/640, 167/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 415498240 421068800 ⟨⟨192801080100, 192801080107⟩, ⟨184018213326, 201780597221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 170393600 421068800 426639360 ⟨⟨195057269366, 195057269374⟩, ⟨186246120882, 204064608946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 173015040 415498240 421068800 ⟨⟨190041813507, 190041813515⟩, ⟨181345376650, 198932807824⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 421068800 426639360 ⟨⟨192273655474, 192273655483⟩, ⟨183548842423, 201192608337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 170393600 426639360 432209920 ⟨⟨197307883850, 197307883858⟩, ⟨188468567895, 206342926203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167772160 170393600 432209920 437780480 ⟨⟨199552999984, 199552999991⟩, ⟨190685628952, 208615627293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 173015040 426639360 432209920 ⟨⟨194500114805, 194500114814⟩, ⟨185747034917, 203446911376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 170393600 173015040 432209920 437780480 ⟨⟨196721264521, 196721264529⟩, ⟨187940025415, 205695791721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 175636480 415498240 421068800 ⟨⟨187313128597, 187313128605⟩, ⟨178701564659, 196117193550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 173015040 175636480 421068800 426639360 ⟨⟨189520591460, 189520591469⟩, ⟨180880573060, 198352733161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 178257920 415498240 421068800 ⟨⟨184614206109, 184614206113⟩, ⟨176086001427, 193332891093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 175636480 178257920 421068800 426639360 ⟨⟨186797262864, 186797262868⟩, ⟨178240540900, 195544125747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 426639360 432209920 ⟨⟨191722858930, 191722858940⟩, ⟨183054490601, 200582967349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 173015040 175636480 432209920 437780480 ⟨⟨193920000754, 193920000763⟩, ⟨185223385392, 202807967517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 175636480 178257920 426639360 432209920 ⟨⟨188975306639, 188975306645⟩, ⟨180390167165, 197750242155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 432209920 437780480 ⟨⟨191148404039, 191148404041⟩, ⟨182534945287, 199951308472⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 415498240 437780480 t = true :=
  ⟨_, (join_su (m := 173015040) (by decide) (join_sr (m := 426639360) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 421068800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 421068800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 170393600) (by decide) (join_sr (m := 432209920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 432209920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 426639360) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 421068800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 421068800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 175636480) (by decide) (join_sr (m := 432209920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 432209920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (317/640 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
