-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r794296320_816578560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:14:40.512864+00:00
-- url     : https://prove2.me/submissions/ae4531aa-e736-4251-9ef8-0b85b735ee65

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [303/320, 623/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 794296320 799866880 ⟨⟨258233510131, 258233510141⟩, ⟨249087492441, 267539026116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 799866880 805437440 ⟨⟨259883332228, 259883332237⟩, ⟨250710760939, 269215222367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 794296320 799866880 ⟨⟨254485145159, 254485145169⟩, ⟨245403748549, 263726061316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 799866880 805437440 ⟨⟨256115301220, 256115301230⟩, ⟨247007326088, 265382642477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 805437440 811008000 ⟨⟨261532189026, 261532189036⟩, ⟨252333069476, 270890442924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 811008000 816578560 ⟨⟨263180100213, 263180100224⟩, ⟨253954437380, 272564707811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 805437440 811008000 ⟨⟨257744527462, 257744527471⟩, ⟨248609977814, 267038284864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 811008000 816578560 ⟨⟨259372842774, 259372842785⟩, ⟨250211722274, 268693007688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 794296320 799866880 ⟨⟨250751253058, 250751253067⟩, ⟨241734124894, 259927900063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 799866880 805437440 ⟨⟨252361638777, 252361638786⟩, ⟨243317916808, 261564751599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 230686720 794296320 799866880 ⟨⟨247031536812, 247031536816⟩, ⟨238078329043, 256144241352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228065280 230686720 799866880 805437440 ⟨⟨248622050543, 248622050548⟩, ⟨239642243138, 257761251592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 225443840 228065280 805437440 811008000 ⟨⟨253971129401, 253971129410⟩, ⟨244900816321, 263200700517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 228065280 811008000 816578560 ⟨⟨255579743046, 255579743056⟩, ⟨246482841226, 264835765233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 230686720 805437440 811008000 ⟨⟨250211703151, 250211703156⟩, ⟨241205297510, 259377394599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 230686720 811008000 816578560 ⟨⟨251800511995, 251800512000⟩, ⟨242767509207, 260992688016⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 794296320 816578560 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 805437440) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 799866880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 799866880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 811008000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 811008000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 805437440) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 799866880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 799866880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 228065280) (by decide) (join_sr (m := 811008000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 811008000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (303/320 : ℝ) (623/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  have e3 : (((816578560 : ℤ) : ℝ) / (D : ℝ)) = (623/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
