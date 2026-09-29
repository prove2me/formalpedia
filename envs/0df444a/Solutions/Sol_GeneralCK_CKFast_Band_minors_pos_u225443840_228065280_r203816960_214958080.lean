-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_228065280_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:04:33.265672+00:00
-- url     : https://prove2.me/submissions/9fb1ba12-4506-466a-a523-df91a07acc57

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 87/320]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226099200 203816960 206602240 ⟨⟨70728730042, 70728730048⟩, ⟨68907558630, 72563356561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226099200 226754560 203816960 206602240 ⟨⟨70421118327, 70421118333⟩, ⟨68604692442, 72250946083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226099200 206602240 209387520 ⟨⟨71650208839, 71650208846⟩, ⟨69825095549, 73488784155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226099200 226754560 206602240 209387520 ⟨⟨71338899731, 71338899738⟩, ⟨69518542038, 73172666363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 226754560 227409920 203816960 206602240 ⟨⟨70114362288, 70114362294⟩, ⟨68302660238, 71939413306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 227409920 228065280 203816960 206602240 ⟨⟨69808455676, 69808455678⟩, ⟨68001455931, 71628751816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 227409920 206602240 209387520 ⟨⟨71028452872, 71028452879⟩, ⟨69212829089, 72857432842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227409920 228065280 206602240 209387520 ⟨⟨70718861980, 70718861984⟩, ⟨68907950578, 72543077145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 226099200 209387520 212172800 ⟨⟨72570783295, 72570783302⟩, ⟨70741732276, 74413303182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226099200 226754560 209387520 212172800 ⟨⟨72255787590, 72255787597⟩, ⟨70431502147, 74093488968⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 225443840 226099200 212172800 214958080 ⟨⟨73490457997, 73490458002⟩, ⟨71657473378, 75336918256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 226099200 226754560 212172800 214958080 ⟨⟨73171786425, 73171786432⟩, ⟨71343577269, 75013418443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226754560 227409920 209387520 212172800 ⟨⟨71941660604, 71941660611⟩, ⟨70122119055, 73774565488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 227409920 228065280 209387520 212172800 ⟨⟨71628396023, 71628396026⟩, ⟨69813576840, 73456526263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 226754560 227409920 212172800 214958080 ⟨⟨72853989938, 72853989943⟩, ⟨71030534566, 74690815721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227409920 228065280 212172800 214958080 ⟨⟨72537062185, 72537062188⟩, ⟨70718339079, 74369103579⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 228065280 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226099200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 227409920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 226754560) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 226099200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 227409920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 227409920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
