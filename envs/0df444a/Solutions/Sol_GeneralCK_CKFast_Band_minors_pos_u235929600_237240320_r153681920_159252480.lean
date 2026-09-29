-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_237240320_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:03:46.310153+00:00
-- url     : https://prove2.me/submissions/d54f9c78-b7ea-4c51-91e9-2e2f47583e88

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 181/640]`, `ρ ∈ [469/2560, 243/1280]` by 11 cells of the computing
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
theorem cell0 : cellOK 235929600 236257280 153681920 155074560 ⟨⟨50076752036, 50076752041⟩, ⟨49235540918, 50921082789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236257280 236584960 153681920 155074560 ⟨⟨49962930116, 49962930121⟩, ⟨49122779359, 50806194211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236584960 155074560 156467200 ⟨⟨50458578916, 50458578922⟩, ⟨49027659683, 51898207457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 236912640 153681920 155074560 ⟨⟨49849267647, 49849267650⟩, ⟨49010174847, 50691467505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 236912640 237240320 153681920 155074560 ⟨⟨49735764026, 49735764032⟩, ⟨48897726787, 50576902072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 236584960 236912640 155074560 156467200 ⟨⟨50286608661, 50286608663⟩, ⟨49446558575, 51129767085⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236912640 237240320 155074560 156467200 ⟨⟨50172161744, 50172161749⟩, ⟨49333168660, 51014256919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235929600 236584960 156467200 157859840 ⟨⟨50897133255, 50897133262⟩, ⟨49464446524, 52338534869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236584960 157859840 159252480 ⟨⟨51335484612, 51335484618⟩, ⟨49901030860, 52778658805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236584960 237240320 156467200 157859840 ⟨⟨50666033611, 50666033616⟩, ⟨49236326424, 52104426189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 236584960 237240320 157859840 159252480 ⟨⟨51102501550, 51102501555⟩, ⟨49671032080, 52542662002⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 237240320 153681920 159252480 t = true :=
  ⟨_, (join_sr (m := 156467200) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 155074560) (by decide) (join_su (m := 236257280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 155074560) (by decide) (join_su (m := 236912640) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 236912640) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 236584960) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 157859840) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (181/640 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
