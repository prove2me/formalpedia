-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r460062720_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:35.669987+00:00
-- url     : https://prove2.me/submissions/cf491909-33f2-4b31-aeb5-ae67a8a019db

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [351/640, 23/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 460062720 465633280 ⟨⟨199081402547, 199081402557⟩, ⟨190409144931, 207939581561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 180879360 465633280 471203840 ⟨⟨201203090375, 201203090384⟩, ⟨192502988688, 210088767457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 183500800 460062720 465633280 ⟨⟨196248762842, 196248762851⟩, ⟨187656563844, 205025215241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 465633280 471203840 ⟨⟨198347309020, 198347309027⟩, ⟨189727197343, 207151363612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 180879360 471203840 476774400 ⟨⟨203320432761, 203320432770⟩, ⟨194592571066, 212233518477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 180879360 476774400 482344960 ⟨⟨205433488059, 205433488069⟩, ⟨196677949122, 214373894284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 180879360 183500800 471203840 476774400 ⟨⟨200441660805, 200441660815⟩, ⟨191793716562, 209273232126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180879360 183500800 476774400 482344960 ⟨⟨202531874004, 202531874013⟩, ⟨193856176085, 211390877817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 186122240 460062720 465633280 ⟨⟨193443347378, 193443347387⟩, ⟨184929922984, 202139379887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 183500800 186122240 465633280 471203840 ⟨⟨195518703853, 195518703860⟩, ⟨186977312055, 204242427483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 188743680 460062720 465633280 ⟨⟨190664469133, 190664469142⟩, ⟨182228567830, 199281355723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186122240 188743680 465633280 471203840 ⟨⟨192716592042, 192716592051⟩, ⟨184252681908, 201361244123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 471203840 476774400 ⟨⟨197590013247, 197590013257⟩, ⟨189020730258, 206341346467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 183500800 186122240 476774400 482344960 ⟨⟨199657328912, 199657328920⟩, ⟨191060229791, 208436191344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 186122240 188743680 471203840 476774400 ⟨⟨194764811492, 194764811501⟩, ⟨186272964887, 203437151422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 476774400 482344960 ⟨⟨196809178467, 196809178476⟩, ⟨188289466675, 205509129687⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 460062720 482344960 t = true :=
  ⟨_, (join_su (m := 183500800) (by decide) (join_sr (m := 471203840) (by decide) (join_su (m := 180879360) (by decide) (join_sr (m := 465633280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 465633280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 180879360) (by decide) (join_sr (m := 476774400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 476774400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 471203840) (by decide) (join_su (m := 186122240) (by decide) (join_sr (m := 465633280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 465633280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 186122240) (by decide) (join_sr (m := 476774400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 476774400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (351/640 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  have e3 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
