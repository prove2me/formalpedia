-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_234618880_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:54:58.297986+00:00
-- url     : https://prove2.me/submissions/31d22faa-c002-40bb-aef2-c08e04a12ba3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 179/640]`, `ρ ∈ [113/640, 469/2560]` by 15 cells of the computing
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
theorem cell0 : cellOK 233308160 233635840 148111360 149504000 ⟨⟨49203667285, 49203667288⟩, ⟨48357777015, 50052723428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233635840 233963520 148111360 149504000 ⟨⟨49092374747, 49092374753⟩, ⟨48247558537, 49940350338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233635840 149504000 150896640 ⟨⟨49651360249, 49651360252⟩, ⟨48804496461, 50501391137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233635840 233963520 149504000 150896640 ⟨⟨49539108953, 49539108958⟩, ⟨48693320703, 50388057819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 233963520 234291200 148111360 149504000 ⟨⟨48981242409, 48981242414⟩, ⟨48137497789, 49828139939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 234291200 234618880 148111360 149504000 ⟨⟨48870269663, 48870269668⟩, ⟨48027594167, 49716091617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233963520 234291200 149504000 150896640 ⟨⟨49427018901, 49427018906⟩, ⟨48582303716, 50274888237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 234291200 234618880 149504000 150896640 ⟨⟨49315089481, 49315089486⟩, ⟨48471444893, 50161881777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233635840 150896640 152289280 ⟨⟨50098836383, 50098836385⟩, ⟨49250999519, 50949841573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233635840 233963520 150896640 152289280 ⟨⟨49985627697, 49985627703⟩, ⟨49138867842, 50835549402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233963520 152289280 153681920 ⟨⟨50488993404, 50488993409⟩, ⟨49049602876, 51937202352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233963520 234291200 150896640 152289280 ⟨⟨49872581292, 49872581298⟩, ⟨49026895972, 50721422004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 234291200 234618880 150896640 152289280 ⟨⟨49759696553, 49759696559⟩, ⟨48915083298, 50607458763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 233963520 234291200 152289280 153681920 ⟨⟨50317930101, 50317930106⟩, ⟨49471275072, 51167741756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234291200 234618880 152289280 153681920 ⟨⟨50204091392, 50204091398⟩, ⟨49358509891, 51052823089⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 234618880 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 233963520) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233635840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 234291200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 233963520) (by decide) (join_sr (m := 152289280) (by decide) (join_su (m := 233635840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 152289280) (by decide) (join_su (m := 234291200) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 234291200) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (179/640 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
