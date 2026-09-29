-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r482344960_504627200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:25:31.81143+00:00
-- url     : https://prove2.me/submissions/8c95285c-e284-4d0e-a807-fd575fab1123

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [23/40, 77/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 482344960 487915520 ⟨⟨149157444340, 149157444348⟩, ⟨144943582223, 153424261425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237240320 238551040 482344960 487915520 ⟨⟨147923613070, 147923613077⟩, ⟨143730061288, 152169857844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 237240320 487915520 493486080 ⟨⟨150762627564, 150762627570⟩, ⟨146534503836, 155043730424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 487915520 493486080 ⟨⟨149517198024, 149517198031⟩, ⟨145309419334, 153777696791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239861760 482344960 487915520 ⟨⟨146693803975, 146693803981⟩, ⟨142520435983, 150919604525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239861760 241172480 482344960 487915520 ⟨⟨145467968826, 145467968834⟩, ⟨141314659399, 149673451908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 238551040 239861760 487915520 493486080 ⟨⟨148275789125, 148275789127⟩, ⟨144088229842, 152515810899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239861760 241172480 487915520 493486080 ⟨⟨147038352798, 147038352804⟩, ⟨142870888601, 151258023380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 237240320 493486080 499056640 ⟨⟨152366063550, 152366063557⟩, ⟨148123689273, 156661440100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 238551040 493486080 499056640 ⟨⟨151109074658, 151109074664⟩, ⟨146887079440, 155383816024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 237240320 499056640 504627200 ⟨⟨153967772272, 153967772281⟩, ⟨149711158321, 158277410606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237240320 238551040 499056640 504627200 ⟨⟨152699262427, 152699262435⟩, ⟨148463060889, 156988235180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 493486080 499056640 ⟨⟨149856104253, 149856104258⟩, ⟨145654363399, 154110336549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 241172480 493486080 499056640 ⟨⟨148607104447, 148607104455⟩, ⟨144425494541, 152840952500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 238551040 239861760 499056640 504627200 ⟨⟨151434768321, 151434768326⟩, ⟨147218855437, 155703200603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 499056640 504627200 ⟨⟨150174242240, 150174242248⟩, ⟨145978495519, 154422257895⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 482344960 504627200 t = true :=
  ⟨_, (join_sr (m := 493486080) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 487915520) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237240320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 487915520) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239861760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 238551040) (by decide) (join_sr (m := 499056640) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 237240320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 499056640) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239861760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (23/40 : ℝ) (77/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((482344960 : ℤ) : ℝ) / (D : ℝ)) = (23/40 : ℝ) := by norm_num [D]
  have e3 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
