-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u231997440_233308160_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:27:56.979292+00:00
-- url     : https://prove2.me/submissions/6a7fd19b-3799-48b4-bc5d-b5099c708d2d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [177/640, 89/320]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 231997440 232325120 142540800 143933440 ⟨⟨47842063004, 47842063010⟩, ⟨46995773985, 48691539246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 232325120 232652800 142540800 143933440 ⟨⟨47733989484, 47733989490⟩, ⟨46888778526, 48582381056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 232325120 143933440 145326080 ⟨⟨48294496446, 48294496453⟩, ⟨47447226121, 49144955211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 232325120 232652800 143933440 145326080 ⟨⟨48185454327, 48185454334⟩, ⟨47339263569, 49034826924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 232652800 232980480 142540800 143933440 ⟨⟨47626074312, 47626074318⟩, ⟨46781938907, 48473383743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 232980480 233308160 142540800 143933440 ⟨⟨47518316885, 47518316890⟩, ⟨46675254537, 48364546694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 232652800 232980480 143933440 145326080 ⟨⟨48076571643, 48076571649⟩, ⟨47231457943, 48924860600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 232980480 233308160 143933440 145326080 ⟨⟨47967847786, 47967847791⟩, ⟨47123808646, 48815055625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232325120 145326080 146718720 ⟨⟨48746705335, 48746705341⟩, ⟨47898454171, 49598146149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 232325120 232652800 145326080 146718720 ⟨⟨48636696032, 48636696037⟩, ⟨47789525936, 49487049184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 231997440 232325120 146718720 148111360 ⟨⟨49198690215, 49198690220⟩, ⟨48349458682, 50051112608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232325120 232652800 146718720 148111360 ⟨⟨49087715137, 49087715142⟩, ⟨48239566165, 49939048381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 232652800 232980480 145326080 146718720 ⟨⟨48526847241, 48526847247⟩, ⟨47680755703, 49376115263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 232980480 233308160 145326080 146718720 ⟨⟨48417158355, 48417158360⟩, ⟨47572142874, 49265343769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 232652800 232980480 146718720 148111360 ⟨⟨48976901645, 48976901651⟩, ⟨48129832724, 49827148273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232980480 233308160 146718720 148111360 ⟨⟨48866249124, 48866249130⟩, ⟨48020257753, 49715411660⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 231997440 233308160 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 232325120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 232325120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 232980480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 232980480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 232652800) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 232325120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 232325120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 232980480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 232980480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (177/640 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((231997440 : ℤ) : ℝ) / (D : ℝ)) = (177/640 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
