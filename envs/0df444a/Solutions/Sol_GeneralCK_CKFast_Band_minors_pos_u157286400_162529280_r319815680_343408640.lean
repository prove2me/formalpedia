-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_162529280_r319815680_343408640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:03:37.109107+00:00
-- url     : https://prove2.me/submissions/a1553c2b-f81c-4a86-80af-a0aee2ebb738

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 31/160]`, `ρ ∈ [61/160, 131/320]` by 15 cells of the computing
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
theorem cell0 : cellOK 157286400 158597120 319815680 325713920 ⟨⟨163334644662, 163334644670⟩, ⟨157930137573, 168823121089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 158597120 159907840 319815680 325713920 ⟨⟨162106660687, 162106660695⟩, ⟨156736082983, 167560508464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 158597120 325713920 331612160 ⟨⟨165966071189, 165966071198⟩, ⟨160544244497, 171471545889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 158597120 159907840 325713920 331612160 ⟨⟨164722978286, 164722978296⟩, ⟨159335045989, 170193871285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159907840 161218560 319815680 325713920 ⟨⟨160887401477, 160887401479⟩, ⟨155550390080, 166306992408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 161218560 162529280 319815680 325713920 ⟨⟨159676733056, 159676733064⟩, ⟨154372930932, 165062432774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 161218560 325713920 331612160 ⟨⟨163488626172, 163488626178⟩, ⟨158134228760, 168925305408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 161218560 162529280 325713920 331612160 ⟨⟨162262881450, 162262881460⟩, ⟨156941665343, 167665708806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 158597120 331612160 337510400 ⟨⟨168588256306, 168588256316⟩, ⟨163149244423, 174110593430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 158597120 159907840 331612160 337510400 ⟨⟨167330222178, 167330222188⟩, ⟨161925066942, 172818027252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 159907840 337510400 343408640 ⟨⟨170563829936, 170563829945⟩, ⟨161713178537, 179633972600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 159907840 161218560 331612160 337510400 ⟨⟨166080942376, 166080942380⟩, ⟨160709287869, 171534579451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 162529280 331612160 337510400 ⟨⟨164840284110, 164840284119⟩, ⟨159501780237, 170260111303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 159907840 161218560 337510400 343408640 ⟨⟨168664482812, 168664482816⟩, ⟨163275697628, 174134949801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161218560 162529280 337510400 343408640 ⟨⟨167409070490, 167409070498⟩, ⟨162053402640, 172845772176⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 162529280 319815680 343408640 t = true :=
  ⟨_, (join_sr (m := 331612160) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 325713920) (by decide) (join_su (m := 158597120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 158597120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 325713920) (by decide) (join_su (m := 161218560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 161218560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 159907840) (by decide) (join_sr (m := 337510400) (by decide) (join_su (m := 158597120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 337510400) (by decide) (join_su (m := 161218560) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 161218560) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (61/160 : ℝ) (131/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  have e3 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
