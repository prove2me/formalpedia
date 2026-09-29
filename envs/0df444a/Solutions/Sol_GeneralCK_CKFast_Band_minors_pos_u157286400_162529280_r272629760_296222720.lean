-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_162529280_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:01:43.736538+00:00
-- url     : https://prove2.me/submissions/754918d2-b23c-4618-bdea-4e909e6e5dcc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 31/160]`, `ρ ∈ [13/40, 113/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 158597120 272629760 278528000 ⟨⟨141933046498, 141933046507⟩, ⟨136672276282, 147280301559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 158597120 159907840 272629760 278528000 ⟨⟨140832409370, 140832409377⟩, ⟨135605738341, 146144768551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 158597120 278528000 284426240 ⟨⟨144643703169, 144643703178⟩, ⟨139364434323, 150009148076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 158597120 159907840 278528000 284426240 ⟨⟨143526482242, 143526482250⟩, ⟨138281302978, 148857053215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159907840 161218560 272629760 278528000 ⟨⟨139740268801, 139740268805⟩, ⟨134547306504, 145018133833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 161218560 162529280 272629760 278528000 ⟨⟨138656487514, 138656487523⟩, ⟨133496850424, 143900252993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 161218560 278528000 284426240 ⟨⟨142417797001, 142417797006⟩, ⟨137206320148, 147713892158⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 161218560 162529280 278528000 284426240 ⟨⟨141317510434, 141317510442⟩, ⟨136139355638, 146579520872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 158597120 284426240 290324480 ⟨⟨147343918230, 147343918237⟩, ⟨142046308834, 152727393216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 158597120 159907840 284426240 290324480 ⟨⟨146210311634, 146210311643⟩, ⟨140946778689, 151558938120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 158597120 290324480 296222720 ⟨⟨150033850408, 150033850415⟩, ⟨144718055346, 155435198944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 158597120 159907840 290324480 296222720 ⟨⟨148884052158, 148884052167⟩, ⟨143602316997, 154250580996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 159907840 161218560 284426240 290324480 ⟨⟨145085276626, 145085276632⟩, ⟨139855436288, 150399449065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161218560 162529280 284426240 290324480 ⟨⟨143968676502, 143968676509⟩, ⟨138772151636, 149248782457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 159907840 161218560 290324480 296222720 ⟨⟨147742858272, 147742858274⟩, ⟨142494802538, 153074958169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161218560 162529280 290324480 296222720 ⟨⟨146610132396, 146610132405⟩, ⟨141395382216, 151908187342⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 162529280 272629760 296222720 t = true :=
  ⟨_, (join_sr (m := 284426240) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 278528000) (by decide) (join_su (m := 158597120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 158597120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 278528000) (by decide) (join_su (m := 161218560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 161218560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 159907840) (by decide) (join_sr (m := 290324480) (by decide) (join_su (m := 158597120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 158597120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290324480) (by decide) (join_su (m := 161218560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 161218560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
