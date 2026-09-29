-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_228065280_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:25:31.166983+00:00
-- url     : https://prove2.me/submissions/e4994b2a-9270-4264-8745-cc3f4ada2e0b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 87/320]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226099200 214958080 217743360 ⟨⟨74409237513, 74409237520⟩, ⟨72572323400, 76259633969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226099200 226754560 214958080 217743360 ⟨⟨74086900735, 74086900742⟩, ⟨72254771881, 75932459308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226099200 217743360 220528640 ⟨⟨75327126394, 75327126401⟩, ⟨73486286867, 77181454893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226099200 226754560 217743360 220528640 ⟨⟨75001135002, 75001135009⟩, ⟨73165090437, 76850616071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 226754560 227409920 214958080 217743360 ⟨⟨73765445303, 73765445310⟩, ⟨71938080034, 75606187994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 227409920 228065280 214958080 217743360 ⟨⟨73444864836, 73444864839⟩, ⟨71622241637, 75280813480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 227409920 217743360 220528640 ⟨⟨74676031114, 74676031121⟩, ⟨72844759847, 76520686742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227409920 228065280 217743360 220528640 ⟨⟨74351808321, 74351808322⟩, ⟨72525288840, 76191660335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226099200 220528640 223313920 ⟨⟨76244129166, 76244129172⟩, ⟨74399368284, 78102385581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226099200 226754560 220528640 223313920 ⟨⟨75914493685, 75914493692⟩, ⟨74074537378, 77767893211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226099200 223313920 226099200 ⟨⟨77160250339, 77160250344⟩, ⟨75311572134, 79022430562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226099200 226754560 223313920 226099200 ⟨⟨76826981223, 76826981230⟩, ⟨74983117119, 78684295191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226754560 227409920 220528640 223313920 ⟨⟨75585751765, 75585751770⟩, ⟨73750578376, 77434316382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 227409920 228065280 220528640 223313920 ⟨⟨75257896965, 75257896968⟩, ⟨73427484994, 77101648491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 226754560 227409920 223313920 226099200 ⟨⟨76494611627, 76494611634⟩, ⟨74655539974, 78347081309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227409920 228065280 223313920 226099200 ⟨⟨76163135079, 76163135082⟩, ⟨74328834386, 78010782280⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 228065280 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226099200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 227409920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 226754560) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226099200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 227409920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
