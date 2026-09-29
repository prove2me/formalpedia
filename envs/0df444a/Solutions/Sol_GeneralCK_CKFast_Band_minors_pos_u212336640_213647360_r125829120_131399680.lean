-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u212336640_213647360_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:12:44.991176+00:00
-- url     : https://prove2.me/submissions/9b6e50ae-a26e-4670-a4cd-fec80cc64068

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [81/320, 163/640]`, `ρ ∈ [3/20, 401/2560]` by 15 cells of the computing
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
theorem cell0 : cellOK 212336640 212664320 125829120 127221760 ⟨⟨48462994155, 48462994160⟩, ⟨47560010989, 49369597490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212664320 212992000 125829120 127221760 ⟨⟨48356847815, 48356847822⟩, ⟨47455092681, 49262214832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 212664320 127221760 128614400 ⟨⟨48979633536, 48979633542⟩, ⟨48075564671, 49887323304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212664320 212992000 127221760 128614400 ⟨⟨48872422868, 48872422874⟩, ⟨47969583740, 49778874622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212992000 213319680 125829120 127221760 ⟨⟨48250884839, 48250884844⟩, ⟨47350354571, 49155018729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 213319680 213647360 125829120 127221760 ⟨⟨48145104486, 48145104491⟩, ⟨47245795938, 49048008428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212992000 213319680 127221760 128614400 ⟨⟨48765397002, 48765397008⟩, ⟨47863784447, 49670613936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 213319680 213647360 127221760 128614400 ⟨⟨48658555195, 48658555201⟩, ⟨47758166063, 49562540491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 212336640 212664320 128614400 130007040 ⟨⟨49495937657, 49495937664⟩, ⟨48590784037, 50404712911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 212664320 212992000 128614400 130007040 ⟨⟨49387664680, 49387664685⟩, ⟨48483742494, 50295200231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 212336640 212992000 130007040 131399680 ⟨⟨49957217288, 49957217295⟩, ⟨48443779168, 51480495573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 212992000 213319680 128614400 130007040 ⟨⟨49279577932, 49279577939⟩, ⟨48376884015, 50185876981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 213319680 213647360 128614400 130007040 ⟨⟨49171676670, 49171676675⟩, ⟨48270207867, 50076742397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 212992000 213319680 130007040 131399680 ⟨⟨49793428526, 49793428532⟩, ⟨48889654166, 50700808760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 213319680 213647360 130007040 131399680 ⟨⟨49684469796, 49684469803⟩, ⟨48781922238, 50590615036⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 212336640 213647360 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 212992000) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 212664320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 212664320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 213319680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 213319680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 212992000) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 212664320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 130007040) (by decide) (join_su (m := 213319680) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 213319680) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (81/320 : ℝ) (163/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((212336640 : ℤ) : ℝ) / (D : ℝ)) = (81/320 : ℝ) := by norm_num [D]
  have e1 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
