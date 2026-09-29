-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u217579520_220200960_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:13:01.630463+00:00
-- url     : https://prove2.me/submissions/cda2f024-74b6-44f8-b063-1fa7a04cd5a2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [83/320, 21/80]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 217579520 218234880 214958080 217743360 ⟨⟨78348419822, 78348419825⟩, ⟨76452331907, 80258648107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 218234880 218890240 214958080 217743360 ⟨⟨78014989483, 78014989489⟩, ⟨76123959923, 79920102641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 217579520 218234880 217743360 220528640 ⟨⟨79310655691, 79310655693⟩, ⟨77410526644, 81224929676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 218234880 218890240 217743360 220528640 ⟨⟨78973494419, 78973494426⟩, ⟨77078433308, 80882643884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 218890240 219545600 214958080 217743360 ⟨⟨77682521331, 77682521338⟩, ⟨75796526413, 79582543439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 219545600 220200960 214958080 217743360 ⟨⟨77351008314, 77351008320⟩, ⟨75470024502, 79245963261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218890240 219545600 217743360 220528640 ⟨⟨78637301867, 78637301874⟩, ⟨76747284991, 80541350870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 219545600 220200960 217743360 220528640 ⟨⟨78302070949, 78302070956⟩, ⟨76417074786, 80201043367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218234880 220528640 223313920 ⟨⟨80271870905, 80271870908⟩, ⟨78367705958, 82190185277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 218234880 218890240 220528640 223313920 ⟨⟨79930990516, 79930990521⟩, ⟨78031902980, 81844171080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 218234880 223313920 226099200 ⟨⟨81232070858, 81232070861⟩, ⟨79323875209, 83154420340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218234880 218890240 223313920 226099200 ⟨⟨80887483086, 80887483092⟩, ⟨78984374221, 82804689575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218890240 219545600 220528640 223313920 ⟨⟨79591085264, 79591085272⟩, ⟨77697051454, 81499156061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 219545600 220200960 220528640 223313920 ⟨⟨79252148036, 79252148043⟩, ⟨77363144444, 81155132926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 219545600 223313920 226099200 ⟨⟨80543876759, 80543876767⟩, ⟨78645831008, 82455964278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219545600 220200960 223313920 226099200 ⟨⟨80201244734, 80201244740⟩, ⟨78308238604, 82108237122⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 217579520 220200960 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 218234880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 219545600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 218890240) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 218234880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 218234880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 219545600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 219545600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (83/320 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
