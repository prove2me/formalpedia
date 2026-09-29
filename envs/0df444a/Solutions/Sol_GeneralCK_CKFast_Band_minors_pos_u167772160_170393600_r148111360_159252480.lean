-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_170393600_r148111360_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:49.262554+00:00
-- url     : https://prove2.me/submissions/e1a973d6-01c2-451d-9b16-a5f76e5c2276

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 13/64]`, `ρ ∈ [113/640, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 168427520 148111360 150896640 ⟨⟨75988097789, 75988097797⟩, ⟨73738866413, 78257629613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 168427520 169082880 148111360 150896640 ⟨⟨75666656838, 75666656839⟩, ⟨73424775229, 77928728175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 168427520 150896640 153681920 ⟨⟨77316784890, 77316784897⟩, ⟨75062416321, 79591435687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 168427520 169082880 150896640 153681920 ⟨⟨76990368073, 76990368076⟩, ⟨74743361498, 79257546720⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 169082880 169738240 148111360 150896640 ⟨⟨75346668027, 75346668035⟩, ⟨73112089450, 77601326591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 169738240 170393600 148111360 150896640 ⟨⟨75028118203, 75028118211⟩, ⟨72800796379, 77275411221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 169082880 169738240 150896640 153681920 ⟨⟨76665418812, 76665418818⟩, ⟨74425727532, 78925172971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 169738240 170393600 150896640 153681920 ⟨⟨76341923854, 76341923862⟩, ⟨74109501632, 78594300706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 168427520 153681920 156467200 ⟨⟨78642704239, 78642704245⟩, ⟨76383220347, 80922451980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 168427520 169082880 153681920 156467200 ⟨⟨78311341955, 78311341960⟩, ⟨76059231966, 80583606202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 168427520 156467200 159252480 ⟨⟨79965875455, 79965875461⟩, ⟨77701297910, 82250698314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 168427520 169082880 156467200 159252480 ⟨⟨79629597805, 79629597809⟩, ⟨77372405757, 81906926141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 169082880 169738240 153681920 156467200 ⟨⟨77981462327, 77981462333⟩, ⟨75736679585, 80246290686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 169738240 170393600 153681920 156467200 ⟨⟨77653052006, 77653052014⟩, ⟨75415550317, 79910491608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 169082880 169738240 156467200 159252480 ⟨⟨79294817597, 79294817605⟩, ⟨77044964438, 81564698959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 169738240 170393600 156467200 159252480 ⟨⟨78961521396, 78961521404⟩, ⟨76718960978, 81224002857⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 170393600 148111360 159252480 t = true :=
  ⟨_, (join_sr (m := 153681920) (by decide) (join_su (m := 169082880) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 168427520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 168427520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 150896640) (by decide) (join_su (m := 169738240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 169738240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 169082880) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 168427520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 168427520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 156467200) (by decide) (join_su (m := 169738240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 169738240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (13/64 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
