-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_235929600_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:56:46.779181+00:00
-- url     : https://prove2.me/submissions/0dfd0ba4-e97a-4b5e-a5ab-4c5d9d0826a8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 9/32]`, `ρ ∈ [469/2560, 243/1280]` by 17 cells of the computing
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
theorem cell0 : cellOK 233308160 233963520 153681920 155074560 ⟨⟨50935559991, 50935559998⟩, ⟨49494381764, 52385562115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233308160 233963520 155074560 156467200 ⟨⟨51381912000, 51381912005⟩, ⟨49938946624, 52833706732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233963520 234618880 153681920 155074560 ⟨⟨50705649751, 50705649754⟩, ⟨49267500518, 52152592533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233963520 234618880 155074560 156467200 ⟨⟨51150097170, 51150097173⟩, ⟨49710165593, 52598827789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233308160 233963520 156467200 157859840 ⟨⟨51828049946, 51828049953⟩, ⟨50383297974, 53281636727⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 233308160 233963520 157859840 159252480 ⟨⟨52273974352, 52273974357⟩, ⟨50827436330, 53729352618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233963520 234618880 156467200 157859840 ⟨⟨51594333218, 51594333221⟩, ⟨50152619831, 53044851129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 233963520 234618880 157859840 159252480 ⟨⟨52038358404, 52038358407⟩, ⟨50594863738, 53490663064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 234618880 235274240 153681920 155074560 ⟨⟨50476393123, 50476393128⟩, ⟨49041257979, 51920291678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 234618880 235274240 155074560 156467200 ⟨⟨50918939995, 50918940002⟩, ⟨49482027304, 52364621621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235274240 235601920 153681920 155074560 ⟨⟨50304876630, 50304876637⟩, ⟨49461537536, 51151348018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 235601920 235929600 153681920 155074560 ⟨⟨50190734005, 50190734012⟩, ⟨49348460112, 51036133854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 235274240 235929600 155074560 156467200 ⟨⟨50688435543, 50688435549⟩, ⟨49254526930, 52131083179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 234618880 235274240 156467200 157859840 ⟨⟨51361278159, 51361278165⟩, ⟨49922588435, 52808742329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235274240 157859840 159252480 ⟨⟨51803408114, 51803408120⟩, ⟨50362941873, 53252654301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235274240 235929600 156467200 157859840 ⟨⟨51128879812, 51128879818⟩, ⟨49693198937, 52573305253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 235274240 235929600 157859840 159252480 ⟨⟨51569118498, 51569118505⟩, ⟨50131665859, 53015321234⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 235929600 153681920 159252480 t = true :=
  ⟨_, (join_su (m := 234618880) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 233963520) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 155074560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 233963520) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 157859840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 156467200) (by decide) (join_su (m := 235274240) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 155074560) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 235274240) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 157859840) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
