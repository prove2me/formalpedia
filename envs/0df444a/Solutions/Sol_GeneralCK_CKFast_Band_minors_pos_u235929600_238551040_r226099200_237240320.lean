-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:34:09.48691+00:00
-- url     : https://prove2.me/submissions/c5fe388d-ffca-4498-ac73-a5cdb450d578

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 226099200 228884480 ⟨⟨72790315289, 72790315294⟩, ⟨71012389350, 74580954385⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 236584960 237240320 226099200 228884480 ⟨⟨72467157380, 72467157386⟩, ⟨70693726870, 74253253831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 236584960 228884480 231669760 ⟨⟨73647555804, 73647555811⟩, ⟨71865871174, 75441962213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 228884480 231669760 ⟨⟨73320873869, 73320873875⟩, ⟨71543694140, 75110728284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 237240320 237895680 226099200 228884480 ⟨⟨72144806833, 72144806836⟩, ⟨70375852461, 73926380201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 237895680 238551040 226099200 228884480 ⟨⟨71823257913, 71823257920⟩, ⟨70058760533, 73600327630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 237895680 228884480 231669760 ⟨⟨72995004625, 72995004628⟩, ⟨71222310512, 74780326603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237895680 238551040 228884480 231669760 ⟨⟨72669942313, 72669942319⟩, ⟨70901714672, 74450751277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 236584960 231669760 234455040 ⟨⟨74504080928, 74504080934⟩, ⟨72718640280, 76302251915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 236584960 237240320 231669760 234455040 ⟨⟨74173883751, 74173883756⟩, ⟨72392957403, 75967493469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 236584960 234455040 237240320 ⟨⟨75359894138, 75359894144⟩, ⟨73570700130, 77161826988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 236584960 237240320 234455040 237240320 ⟨⟨75026190449, 75026190456⟩, ⟨73241520070, 76823552829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 231669760 234455040 ⟨⟨73844504509, 73844504510⟩, ⟨72068073182, 75633572509⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237895680 238551040 231669760 234455040 ⟨⟨73515937416, 73515937421⟩, ⟨71743981972, 75300483115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237240320 237895680 234455040 237240320 ⟨⟨74693309854, 74693309858⟩, ⟨72913143830, 76486121307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 237895680 238551040 234455040 237240320 ⟨⟨74361246544, 74361246549⟩, ⟨72585565741, 76149526477⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 236584960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 236584960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 237895680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 237240320) (by decide) (join_sr (m := 234455040) (by decide) (join_su (m := 236584960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 236584960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 234455040) (by decide) (join_su (m := 237895680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 237895680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
