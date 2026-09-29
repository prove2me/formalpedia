-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_133693440_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:01:44.840291+00:00
-- url     : https://prove2.me/submissions/cc0bbdbd-e936-4276-a2bd-93da4a7a36cb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 51/320]`, `ρ ∈ [31/256, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 131072000 131727360 101580800 103055360 ⟨⟨68273617910, 68273617919⟩, ⟨66128955061, 70437571292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 131072000 131727360 103055360 104529920 ⟨⟨69189899238, 69189899245⟩, ⟨67042142997, 71356928490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131727360 132382720 101580800 103055360 ⟨⟨67954701202, 67954701211⟩, ⟨65818094120, 70110467834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 131727360 132382720 103055360 104529920 ⟨⟨68867230094, 68867230101⟩, ⟨66727537824, 71026064856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131072000 131727360 104529920 106004480 ⟨⟨70104492724, 70104492731⟩, ⟨67953656184, 72274584692⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 131072000 131727360 106004480 107479040 ⟨⟨71017407005, 71017407012⟩, ⟨68863503164, 73190548631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131727360 132382720 104529920 106004480 ⟨⟨69778090908, 69778090915⟩, ⟨67635326347, 71939980841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 131727360 132382720 106004480 107479040 ⟨⟨70687292137, 70687292144⟩, ⟨68541468090, 72852224374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 132382720 133038080 101580800 103055360 ⟨⟨67637846454, 67637846459⟩, ⟨65509226035, 69785496947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 132382720 133038080 103055360 104529920 ⟨⟨68546641047, 68546641052⟩, ⟨66414943672, 70697351892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133038080 133693440 101580800 103055360 ⟨⟨67323029678, 67323029687⟩, ⟨65202327720, 69462633729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 133038080 133693440 103055360 104529920 ⟨⟨68228107957, 68228107964⟩, ⟨66104337302, 70370764543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 132382720 133038080 104529920 106004480 ⟨⟨69453787084, 69453787085⟩, ⟨67319025457, 71607545511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 132382720 133038080 106004480 107479040 ⟨⟨70359292904, 70359292910⟩, ⟨68221479644, 72516086243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 133038080 133693440 104529920 106004480 ⟨⟨69131556955, 69131556962⟩, ⟨67004730121, 71277253499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133038080 133693440 106004480 107479040 ⟨⟨70033384873, 70033384882⟩, ⟨67903514289, 72182108887⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 133693440 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 132382720) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 131727360) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 103055360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 131727360) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 106004480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 104529920) (by decide) (join_su (m := 133038080) (by decide) (join_sr (m := 103055360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 103055360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 133038080) (by decide) (join_sr (m := 106004480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 106004480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (51/320 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((133693440 : ℤ) : ℝ) / (D : ℝ)) = (51/320 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
