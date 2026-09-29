-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:18:50.444296+00:00
-- url     : https://prove2.me/submissions/78856d8e-07fb-4aae-b377-69f334a6b9a7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 214958080 217743360 ⟨⟨103524462643, 103524462648⟩, ⟨99742407964, 107357286420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173015040 174325760 217743360 220528640 ⟨⟨104755371338, 104755371340⟩, ⟨100964901394, 108596590224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 174325760 175636480 214958080 217743360 ⟨⟨102688732747, 102688732753⟩, ⟨98927471726, 106500333217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 217743360 220528640 ⟨⟨103911156293, 103911156302⟩, ⟨100141503807, 107731130398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 174325760 220528640 223313920 ⟨⟨105984139359, 105984139363⟩, ⟨102185277997, 109833729062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 173015040 174325760 223313920 226099200 ⟨⟨107210781037, 107210781042⟩, ⟨103403551913, 111068717452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 174325760 175636480 220528640 223313920 ⟨⟨105131483482, 105131483489⟩, ⟨101353462703, 108959807601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 174325760 175636480 223313920 226099200 ⟨⟨106349728235, 106349728243⟩, ⟨102563362156, 110186378934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 175636480 176947200 214958080 217743360 ⟨⟨101859446167, 101859446175⟩, ⟨98118731438, 105650077197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 175636480 176947200 217743360 220528640 ⟨⟨103073419337, 103073419345⟩, ⟨99324337446, 106872401950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 176947200 178257920 214958080 217743360 ⟨⟨101036497730, 101036497738⟩, ⟨97316086344, 104806408634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 176947200 178257920 217743360 220528640 ⟨⟨102242055042, 102242055050⟩, ⟨98513301283, 106020294926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 175636480 176947200 220528640 223313920 ⟨⟨104285339644, 104285339652⟩, ⟨100527913106, 108092650883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 176947200 223313920 226099200 ⟨⟨105495220623, 105495220629⟩, ⟨101729471779, 109310837707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 176947200 178257920 220528640 223313920 ⟨⟨103445602187, 103445602193⟩, ⟨99708527924, 107232148746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 176947200 178257920 223313920 226099200 ⟨⟨104647152319, 104647152325⟩, ⟨100901779254, 108441983419⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 214958080 226099200 t = true :=
  ⟨_, (join_su (m := 175636480) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 174325760) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 217743360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 174325760) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 223313920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 176947200) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 217743360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 176947200) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 223313920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
