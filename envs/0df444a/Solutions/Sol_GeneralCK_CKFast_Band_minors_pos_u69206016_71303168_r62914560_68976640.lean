-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u69206016_71303168_r62914560_68976640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:24:29.230411+00:00
-- url     : https://prove2.me/submissions/793d535c-c768-46cb-ab10-717b3c34f4c3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/400, 17/200]`, `ρ ∈ [3/40, 421/5120]` by 16 cells of the computing
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
theorem cell0 : cellOK 69206016 69730304 62914560 64430080 ⟨⟨75003638694, 75003638706⟩, ⟨72088134065, 77956894985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 69206016 69730304 64430080 65945600 ⟨⟨76593955055, 76593955065⟩, ⟨73674437005, 79551071387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 69730304 70254592 62914560 64430080 ⟨⟨74582415974, 74582415983⟩, ⟨71683732079, 77518444411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69730304 70254592 64430080 65945600 ⟨⟨76165447282, 76165447294⟩, ⟨73262747389, 79105341752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 69206016 69730304 65945600 67461120 ⟨⟨78176655142, 78176655155⟩, ⟨75253201302, 81137554350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 69206016 69730304 67461120 68976640 ⟨⟨79751820687, 79751820700⟩, ⟨76824507232, 82716427061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 69730304 70254592 65945600 67461120 ⟨⟨77740959257, 77740959266⟩, ⟨74834319807, 80684643755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 69730304 70254592 67461120 68976640 ⟨⟨79309032018, 79309032028⟩, ⟨76398528037, 82256431962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 70254592 70778880 62914560 64430080 ⟨⟨74165592943, 74165592955⟩, ⟨71283515541, 77084614812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 70254592 70778880 64430080 65945600 ⟨⟨75741393960, 75741393970⟩, ⟨72855298600, 78664287141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 70778880 71303168 62914560 64430080 ⟨⟨73753094793, 73753094802⟩, ⟨70887413766, 76655327080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 70778880 71303168 64430080 65945600 ⟨⟨75321719667, 75321719676⟩, ⟨72452019318, 78227827868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 70254592 70778880 65945600 67461120 ⟨⟨77309771026, 77309771038⟩, ⟨74419732984, 80236460660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 70254592 70778880 67461120 68976640 ⟨⟨78870802700, 78870802712⟩, ⟨75976895870, 81801215317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 70778880 71303168 65945600 67461120 ⟨⟨76883014462, 76883014472⟩, ⟨74009368921, 79792924841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 70778880 71303168 67461120 68976640 ⟨⟨78437056202, 78437056212⟩, ⟨75559538251, 81350696379⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 69206016 71303168 62914560 68976640 t = true :=
  ⟨_, (join_su (m := 70254592) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 69730304) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 64430080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 69730304) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 67461120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 65945600) (by decide) (join_su (m := 70778880) (by decide) (join_sr (m := 64430080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 64430080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 70778880) (by decide) (join_sr (m := 67461120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 67461120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/400 : ℝ) (17/200 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (421/5120 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((69206016 : ℤ) : ℝ) / (D : ℝ)) = (33/400 : ℝ) := by norm_num [D]
  have e1 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((68976640 : ℤ) : ℝ) / (D : ℝ)) = (421/5120 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
