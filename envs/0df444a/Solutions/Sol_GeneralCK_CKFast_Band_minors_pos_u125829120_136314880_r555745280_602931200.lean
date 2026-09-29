-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r555745280_602931200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:53:17.480356+00:00
-- url     : https://prove2.me/submissions/873b3f91-ba12-43a6-8c4c-ecf24f21c63d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [53/80, 23/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 555745280 567541760 ⟨⟨307116759710, 307116759721⟩, ⟨293557996650, 320978491375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 128450560 131072000 555745280 567541760 ⟨⟨303215095803, 303215095815⟩, ⟨289802609801, 316928695152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 128450560 567541760 579338240 ⟨⟨312273163780, 312273163791⟩, ⟨298673168180, 326170916165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 567541760 579338240 ⟨⟨308334847207, 308334847218⟩, ⟨294879577073, 322086243422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131072000 133693440 555745280 567541760 ⟨⟨299356472368, 299356472379⟩, ⟨286087995281, 312924176727⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 133693440 136314880 555745280 567541760 ⟨⟨295539721221, 295539721233⟩, ⟨282413043596, 308963712407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131072000 133693440 567541760 579338240 ⟨⟨304439027427, 304439027438⟩, ⟨291126298452, 318046214295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 133693440 136314880 567541760 579338240 ⟨⟨300584560700, 300584560712⟩, ⟨287412244055, 314049632909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 128450560 579338240 591134720 ⟨⟨317402824189, 317402824201⟩, ⟨303762140339, 331336068029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 128450560 131072000 579338240 591134720 ⟨⟨313428523635, 313428523646⟩, ⟨299931013208, 327217183562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 128450560 591134720 602931200 ⟨⟨322506707676, 322506707687⟩, ⟨308825850881, 336474941553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 128450560 131072000 591134720 602931200 ⟨⟨318497059229, 318497059241⟩, ⟨304957824179, 332322476883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131072000 133693440 579338240 591134720 ⟨⟨309496169647, 309496169659⟩, ⟨296139730593, 323142303890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133693440 136314880 579338240 591134720 ⟨⟨305604642465, 305604642477⟩, ⟨292387225136, 319110260344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 131072000 133693440 591134720 602931200 ⟨⟨314528801385, 314528801396⟩, ⟨301129166725, 328213374328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 136314880 591134720 602931200 ⟨⟨310600837898, 310600837910⟩, ⟨297338831730, 324146491817⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 555745280 602931200 t = true :=
  ⟨_, (join_sr (m := 579338240) (by decide) (join_su (m := 131072000) (by decide) (join_sr (m := 567541760) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 128450560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 567541760) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 133693440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 131072000) (by decide) (join_sr (m := 591134720) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 128450560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 591134720) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 133693440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (53/80 : ℝ) (23/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((555745280 : ℤ) : ℝ) / (D : ℝ)) = (53/80 : ℝ) := by norm_num [D]
  have e3 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
