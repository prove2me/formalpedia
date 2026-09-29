-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_183500800_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:33.637707+00:00
-- url     : https://prove2.me/submissions/c216ba13-1841-48fc-ae37-2c2b406c117c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 7/32]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 179568640 203816960 206602240 ⟨⟨95411140142, 95411140148⟩, ⟨91744277601, 99127132366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178257920 179568640 206602240 209387520 ⟨⟨96616318542, 96616318550⟩, ⟨92941052287, 100340704958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 179568640 180879360 203816960 206602240 ⟨⟨94634370122, 94634370124⟩, ⟨90987228758, 98330228527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 179568640 180879360 206602240 209387520 ⟨⟨95831032716, 95831032720⟩, ⟨92175515880, 99535259114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 178257920 179568640 209387520 212172800 ⟨⟨97819476641, 97819476647⟩, ⟨94135828569, 101552234909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 178257920 179568640 212172800 214958080 ⟨⟨99020627585, 99020627591⟩, ⟨95328619428, 102761735541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180879360 209387520 212172800 ⟨⟨97025717623, 97025717626⟩, ⟨93361846565, 100738290328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 179568640 180879360 212172800 214958080 ⟨⟨98218437617, 98218437620⟩, ⟨94546233426, 101939335111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180879360 182190080 203816960 206602240 ⟨⟨93863492700, 93863492706⟩, ⟨90235840660, 97539455373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 182190080 206602240 209387520 ⟨⟨95051676378, 95051676384⟩, ⟨91415677476, 98735980415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 182190080 183500800 203816960 206602240 ⟨⟨93098412217, 93098412223⟩, ⟨89490021734, 96754713025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 182190080 183500800 206602240 209387520 ⟨⟨94278153553, 94278153559⟩, ⟨90661445169, 97942768690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 180879360 182190080 209387520 212172800 ⟨⟨96237924184, 96237924192⟩, ⟨92593599037, 99930548542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 180879360 182190080 212172800 214958080 ⟨⟨97422248529, 97422248537⟩, ⟨93769617598, 101123172323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182190080 183500800 209387520 212172800 ⟨⟨95456000050, 95456000056⟩, ⟨91830993758, 99128909098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182190080 183500800 212172800 214958080 ⟨⟨96631963764, 96631963771⟩, ⟨92998679413, 100313146460⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 183500800 203816960 214958080 t = true :=
  ⟨_, (join_su (m := 180879360) (by decide) (join_sr (m := 209387520) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 206602240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 179568640) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 212172800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 209387520) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 206602240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 206602240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 182190080) (by decide) (join_sr (m := 212172800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 212172800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
