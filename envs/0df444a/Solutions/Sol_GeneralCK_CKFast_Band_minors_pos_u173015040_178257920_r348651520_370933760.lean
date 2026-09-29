-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r348651520_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.335668+00:00
-- url     : https://prove2.me/submissions/55eb5b29-fcdf-47d0-9708-22bf4cedeee9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [133/320, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 348651520 354222080 ⟨⟨160994042774, 160994042777⟩, ⟨155988431346, 166071891225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 174325760 175636480 348651520 354222080 ⟨⟨159791395525, 159791395533⟩, ⟨154814803661, 164839692646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173015040 174325760 354222080 359792640 ⟨⟨163276323492, 163276323497⟩, ⟨158254742530, 168369961801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 354222080 359792640 ⟨⟨162060234782, 162060234791⟩, ⟨157067664642, 167124338390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 175636480 176947200 348651520 354222080 ⟨⟨158596108974, 158596108981⟩, ⟨153648258042, 163615139218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 176947200 178257920 348651520 354222080 ⟨⟨157408078335, 157408078342⟩, ⟨152488693894, 162398121892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 175636480 176947200 354222080 359792640 ⟨⟨160851517608, 160851517617⟩, ⟨155887682037, 165886368409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 176947200 178257920 354222080 359792640 ⟨⟨159650067580, 159650067589⟩, ⟨154714694444, 164655943272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 174325760 359792640 365363200 ⟨⟨165552446850, 165552446855⟩, ⟨160514978718, 170661791110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 174325760 175636480 359792640 365363200 ⟨⟨164323030692, 164323030701⟩, ⟨159314562758, 169402858753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 173015040 174325760 365363200 370933760 ⟨⟨167822494391, 167822494396⟩, ⟨162769220099, 172947462059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 174325760 175636480 365363200 370933760 ⟨⟨166579862816, 166579862825⟩, ⟨161555576263, 171675334616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 175636480 176947200 359792640 365363200 ⟨⟨163100995243, 163100995253⟩, ⟨158121253651, 168151586420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 176947200 178257920 359792640 365363200 ⟨⟨161886236529, 161886236536⟩, ⟨156934951472, 166907866008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 175636480 176947200 365363200 370933760 ⟨⟨165344619504, 165344619513⟩, ⟨160349049247, 170410872152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 176947200 178257920 365363200 370933760 ⟨⟨164116660908, 164116660917⟩, ⟨159149539485, 169153967069⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 348651520 370933760 t = true :=
  ⟨_, (join_sr (m := 359792640) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 174325760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 174325760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 354222080) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 176947200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 175636480) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 174325760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 174325760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 365363200) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 176947200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
