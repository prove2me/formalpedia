-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r508559360_555745280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:53:00.406586+00:00
-- url     : https://prove2.me/submissions/61357685-eb1a-4615-b41f-17d77f67b5a4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [97/160, 53/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 508559360 520355840 ⟨⟨286203350214, 286203350223⟩, ⟨272815588890, 299915099278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 128450560 131072000 508559360 520355840 ⟨⟨282455689398, 282455689409⟩, ⟨269220388036, 296012178788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 128450560 520355840 532152320 ⟨⟨291476984459, 291476984470⟩, ⟨278045495335, 305227178679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 520355840 532152320 ⟨⟨287689639338, 287689639349⟩, ⟨274409070073, 301286357320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131072000 133693440 508559360 520355840 ⟨⟨278753159643, 278753159654⟩, ⟨265667698718, 292157008397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 133693440 136314880 508559360 520355840 ⟨⟨275094490560, 275094490570⟩, ⟨262156323527, 288348247032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131072000 133693440 520355840 532152320 ⟨⟨283946917301, 283946917311⟩, ⟨270814738641, 297392679651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 133693440 136314880 520355840 532152320 ⟨⟨280247574151, 280247574163⟩, ⟨267261326024, 293544834848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 128450560 532152320 543948800 ⟨⟨296719710461, 296719710472⟩, ⟨283245168113, 310507694507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 128450560 131072000 532152320 543948800 ⟨⟨292893495805, 292893495817⟩, ⟨279568328719, 306529786638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 128450560 543948800 555745280 ⟨⟨301932616879, 301932616891⟩, ⟨288415660983, 315757769327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 128450560 131072000 543948800 555745280 ⟨⟨298068308398, 298068308409⟩, ⟨284699179813, 311743549240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131072000 133693440 532152320 543948800 ⟨⟨289111385754, 289111385765⟩, ⟨275933153325, 302598407563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133693440 136314880 532152320 543948800 ⟨⟨285372161884, 285372161895⟩, ⟨272338489044, 298712276109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 131072000 133693440 543948800 555745280 ⟨⟨294247576640, 294247576651⟩, ⟨281023921796, 307775235652⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 136314880 543948800 555745280 ⟨⟨290469228527, 290469228538⟩, ⟨277388755893, 303851576432⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 508559360 555745280 t = true :=
  ⟨_, (join_sr (m := 532152320) (by decide) (join_su (m := 131072000) (by decide) (join_sr (m := 520355840) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 128450560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 520355840) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 133693440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 131072000) (by decide) (join_sr (m := 543948800) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 128450560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 543948800) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 133693440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (97/160 : ℝ) (53/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  have e3 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
