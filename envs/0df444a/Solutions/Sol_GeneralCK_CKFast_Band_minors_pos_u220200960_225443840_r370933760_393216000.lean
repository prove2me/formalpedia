-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r370933760_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:18:54.955163+00:00
-- url     : https://prove2.me/submissions/924a7fb3-3a5a-42b9-8aff-e374454eeb2d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [283/640, 15/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 370933760 376504320 ⟨⟨128893160803, 128893160811⟩, ⟨124721864096, 133120744433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 221511680 222822400 370933760 376504320 ⟨⟨127849270280, 127849270288⟩, ⟨123699284150, 132055190757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 221511680 376504320 382074880 ⟨⟨130688605176, 130688605184⟩, ⟨126502242533, 134931263049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 376504320 382074880 ⟨⟨129632066014, 129632066020⟩, ⟨125467054648, 133853023430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 224133120 370933760 376504320 ⟨⟨126809941414, 126809941422⟩, ⟨122681100982, 130994366838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 224133120 225443840 370933760 376504320 ⟨⟨125775115425, 125775115433⟩, ⟨121667257875, 129938211789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 224133120 376504320 382074880 ⟨⟨128580101296, 128580101302⟩, ⟨124436277234, 132779525373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224133120 225443840 376504320 382074880 ⟨⟨127532652307, 127532652315⟩, ⟨123409853612, 131710708084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 221511680 382074880 387645440 ⟨⟨132481201263, 132481201270⟩, ⟨128279799186, 136738905663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221511680 222822400 382074880 387645440 ⟨⟨131412074957, 131412074965⟩, ⟨127232063801, 135648042678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 221511680 387645440 393216000 ⟨⟨134270980436, 134270980444⟩, ⟨130054565086, 138543703994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 221511680 222822400 387645440 393216000 ⟨⟨133189327664, 133189327670⟩, ⟨128994341828, 137440279384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 382074880 387645440 ⟨⟨130347534885, 130347534893⟩, ⟨126188751595, 134561932042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 225443840 382074880 387645440 ⟨⟨129287522410, 129287522416⟩, ⟨125149805945, 133480513066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 222822400 224133120 387645440 393216000 ⟨⟨132112271933, 132112271939⟩, ⟨127938553498, 136341616911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224133120 225443840 387645440 393216000 ⟨⟨131039754693, 131039754701⟩, ⟨126887143533, 135247656004⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 370933760 393216000 t = true :=
  ⟨_, (join_sr (m := 382074880) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 221511680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 221511680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 376504320) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 224133120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 222822400) (by decide) (join_sr (m := 387645440) (by decide) (join_su (m := 221511680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 221511680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 387645440) (by decide) (join_su (m := 224133120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 224133120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
