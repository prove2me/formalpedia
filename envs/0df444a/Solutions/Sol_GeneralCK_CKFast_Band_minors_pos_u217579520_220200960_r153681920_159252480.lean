-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_220200960_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:38:25.579241+00:00
-- url     : https://prove2.me/submissions/027b7eff-7fa6-4bf9-95f8-3bbf776e8708

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 21/80]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 217579520 218234880 153681920 155074560 ⟨⟨56663037693, 56663037696⟩, ⟨55144383551, 58191309520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 217579520 218234880 155074560 156467200 ⟨⟨57156380456, 57156380458⟩, ⟨55635821383, 58686561751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 218234880 218890240 153681920 155074560 ⟨⟨56415850476, 56415850482⟩, ⟨54900619348, 57940663515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 218234880 218890240 155074560 156467200 ⟨⟨56907183711, 56907183718⟩, ⟨55390052651, 58433901267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 217579520 218234880 156467200 157859840 ⟨⟨57649435499, 57649435502⟩, ⟨56126972546, 59181525198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 217579520 218234880 157859840 159252480 ⟨⟨58142203579, 58142203582⟩, ⟨56617837792, 59676200619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218234880 218890240 156467200 157859840 ⟨⟨57398232674, 57398232681⟩, ⟨55879202706, 58926853706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218234880 218890240 157859840 159252480 ⟨⟨57888998109, 57888998116⟩, ⟨56368070256, 59419521577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 218890240 219545600 153681920 155074560 ⟨⟨56169448539, 56169448545⟩, ⟨54657622498, 57690820964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 218890240 219545600 155074560 156467200 ⟨⟨56658776937, 56658776944⟩, ⟨55145055955, 58182048934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 219545600 220200960 153681920 155074560 ⟨⟨55923825813, 55923825820⟩, ⟨54415387074, 57441775658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 219545600 220200960 155074560 156467200 ⟨⟨56411154036, 56411154043⟩, ⟨54900825338, 57930998515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218890240 219545600 156467200 157859840 ⟨⟨57147824475, 57147824481⟩, ⟨55632209551, 58672995028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218890240 219545600 157859840 159252480 ⟨⟨57636591883, 57636591890⟩, ⟨56119084016, 59163659977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 219545600 220200960 156467200 157859840 ⟨⟨56898204774, 56898204781⟩, ⟨55385987094, 58419942894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219545600 220200960 157859840 159252480 ⟨⟨57384978750, 57384978755⟩, ⟨55870873062, 58908609519⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 220200960 153681920 159252480 t = true :=
  ⟨_, (join_su (m := 218890240) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 218234880) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 155074560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 218234880) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 157859840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 156467200) (by decide) (join_su (m := 219545600) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 155074560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 219545600) (by decide) (join_sr (m := 157859840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 157859840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
