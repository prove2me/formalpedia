-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r348651520_359792640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:50:33.114145+00:00
-- url     : https://prove2.me/submissions/efabdafe-7361-4fb5-bcfb-9c8932ffcb18

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [133/320, 549/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 348651520 351436800 ⟨⟨109641023184, 109641023191⟩, ⟨106307161298, 113012345703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 237240320 351436800 354222080 ⟨⟨110468314114, 110468314121⟩, ⟨107127620807, 113846499923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 238551040 348651520 351436800 ⟨⟨108701830601, 108701830608⟩, ⟨105381845703, 112059085463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 351436800 354222080 ⟨⟨109522758468, 109522758475⟩, ⟨106195964854, 112886854711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 237240320 354222080 357007360 ⟨⟨111295034174, 111295034181⟩, ⟨107947511935, 114680080590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 237240320 357007360 359792640 ⟨⟨112121186294, 112121186302⟩, ⟨108766837598, 115513090648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 238551040 354222080 357007360 ⟨⟨110343128791, 110343128797⟩, ⟨107009528767, 113714063917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237240320 238551040 357007360 359792640 ⟨⟨111162944417, 111162944424⟩, ⟨107822540276, 114540715948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239861760 348651520 351436800 ⟨⟨107766478296, 107766478301⟩, ⟨104460260919, 111109776803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238551040 239861760 351436800 354222080 ⟨⟨108581051746, 108581051750⟩, ⟨105268048587, 111931169473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 241172480 348651520 351436800 ⟨⟨106834916334, 106834916340⟩, ⟨103542358370, 110164368405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 241172480 351436800 354222080 ⟨⟨107643143988, 107643143995⟩, ⟨104343823405, 110979392877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 354222080 357007360 ⟨⟨109395080742, 109395080747⟩, ⟨106075293931, 112752015377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238551040 239861760 357007360 359792640 ⟨⟨110208568057, 110208568059⟩, ⟨106881999704, 113572317300⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 241172480 354222080 357007360 ⟨⟨108450840051, 108450840057⟩, ⟨105144758799, 111793883624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 357007360 359792640 ⟨⟨109258007213, 109258007220⟩, ⟨105945167232, 112607843351⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 348651520 359792640 t = true :=
  ⟨_, (join_su (m := 238551040) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 351436800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 351436800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 237240320) (by decide) (join_sr (m := 357007360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 357007360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 354222080) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 351436800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 351436800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 239861760) (by decide) (join_sr (m := 357007360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 357007360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (549/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((359792640 : ℤ) : ℝ) / (D : ℝ)) = (549/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
