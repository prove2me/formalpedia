-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r337510400_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:49:21.815706+00:00
-- url     : https://prove2.me/submissions/6f974625-1ac4-46f6-a94f-f18df3208f29

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [103/256, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 337510400 340295680 ⟨⟨102694291400, 102694291407⟩, ⟨99442261115, 105982889068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 242483200 340295680 343080960 ⟨⟨103498284025, 103498284031⟩, ⟨100239507239, 106793663828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 243793920 337510400 340295680 ⟨⟨101795603017, 101795603024⟩, ⟨98556923841, 105070663266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 340295680 343080960 ⟨⟨102593216635, 102593216643⟩, ⟨99347815231, 105875035452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 242483200 343080960 345866240 ⟨⟨104301747141, 104301747147⟩, ⟨101036225689, 107603907070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 242483200 345866240 348651520 ⟨⟨105104683398, 105104683404⟩, ⟨101832419105, 108413621456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243793920 343080960 345866240 ⟨⟨103390313454, 103390313460⟩, ⟨100138191483, 106678889005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242483200 243793920 345866240 348651520 ⟨⟨104186896045, 104186896052⟩, ⟨100928055162, 107482226509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 245104640 337510400 340295680 ⟨⟨100900522636, 100900522643⟩, ⟨97675089611, 104162152241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 243793920 245104640 340295680 343080960 ⟨⟨101691766698, 101691766704⟩, ⟨98459635905, 104960131096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 246415360 337510400 340295680 ⟨⟨100009003023, 100009003026⟩, ⟨96796712481, 103257307438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245104640 246415360 340295680 343080960 ⟨⟨100793886935, 100793886939⟩, ⟨97574923273, 104048902166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 343080960 345866240 ⟨⟨102482506438, 102482506445⟩, ⟨99243679374, 105757603965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243793920 245104640 345866240 348651520 ⟨⟨103272744356, 103272744363⟩, ⟨100027222506, 106554573363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 246415360 343080960 345866240 ⟨⟨101578278779, 101578278780⟩, ⟨98352643328, 104840003329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 345866240 348651520 ⟨⟨102362180979, 102362180983⟩, ⟨99129875063, 105630613368⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 337510400 348651520 t = true :=
  ⟨_, (join_su (m := 243793920) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 340295680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 242483200) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 345866240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 343080960) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 340295680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245104640) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 345866240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (103/256 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
