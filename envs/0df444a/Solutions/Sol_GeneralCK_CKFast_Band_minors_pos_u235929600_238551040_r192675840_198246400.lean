-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_238551040_r192675840_198246400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:50:56.236529+00:00
-- url     : https://prove2.me/submissions/24733b9a-6f7a-411d-8683-00f2d90e619c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 91/320]`, `ρ ∈ [147/640, 121/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 236584960 192675840 194068480 ⟨⟨62229699120, 62229699125⟩, ⟨60751222734, 63717031390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 236584960 194068480 195461120 ⟨⟨62662940120, 62662940125⟩, ⟨61182708805, 64152032593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 236584960 237240320 192675840 194068480 ⟨⟨61950444195, 61950444200⟩, ⟨60475065253, 63434650347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 236584960 237240320 194068480 195461120 ⟨⟨62381865994, 62381866000⟩, ⟨60904736445, 63867828060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 236584960 195461120 196853760 ⟨⟨63095990875, 63095990880⟩, ⟨61614005082, 64586843089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 236584960 196853760 198246400 ⟨⟨63528851843, 63528851849⟩, ⟨62045112019, 65021463339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 236584960 237240320 195461120 196853760 ⟨⟨62813099919, 62813099925⟩, ⟨61334220196, 64300817456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 236584960 237240320 196853760 198246400 ⟨⟨63244146421, 63244146427⟩, ⟨61763516958, 64733618984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 237240320 237895680 192675840 194068480 ⟨⟨61671924100, 61671924103⟩, ⟨60199627967, 63153018947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 237895680 194068480 195461120 ⟨⟨62101529932, 62101529933⟩, ⟨60627487508, 63584376407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 237895680 238551040 192675840 194068480 ⟨⟨61394133488, 61394133494⟩, ⟨59924905635, 62872131743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237895680 238551040 194068480 195461120 ⟨⟨61821926565, 61821926570⟩, ⟨60350956738, 63301672166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 237240320 237895680 195461120 196853760 ⟨⟨62530950235, 62530950238⟩, ⟨61055161941, 64015547911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 237240320 237895680 196853760 198246400 ⟨⟨62960185456, 62960185458⟩, ⟨61482651709, 64446533903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 237895680 238551040 195461120 196853760 ⟨⟨62249536437, 62249536443⟩, ⟨60776825040, 63731028970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 237895680 238551040 196853760 198246400 ⟨⟨62676963544, 62676963550⟩, ⟨61202510980, 64160202595⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 238551040 192675840 198246400 t = true :=
  ⟨_, (join_su (m := 237240320) (by decide) (join_sr (m := 195461120) (by decide) (join_su (m := 236584960) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 194068480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 236584960) (by decide) (join_sr (m := 196853760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 196853760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 195461120) (by decide) (join_su (m := 237895680) (by decide) (join_sr (m := 194068480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 194068480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 237895680) (by decide) (join_sr (m := 196853760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 196853760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (147/640 : ℝ) (121/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e2 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  have e3 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
