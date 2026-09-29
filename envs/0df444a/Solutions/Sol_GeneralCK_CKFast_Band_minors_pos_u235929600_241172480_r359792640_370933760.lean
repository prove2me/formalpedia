-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r359792640_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:55:50.484686+00:00
-- url     : https://prove2.me/submissions/b1e0abdc-db4e-4b02-98a8-1411b3ba46f3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [549/1280, 283/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 359792640 362577920 ⟨⟨112946773396, 112946773403⟩, ⟨109585600698, 116345533040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 237240320 362577920 365363200 ⟨⟨113771798389, 113771798397⟩, ⟨110403804129, 117177410688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 238551040 359792640 362577920 ⟨⟨111982208189, 111982208195⟩, ⟨108635002204, 115366813658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 362577920 365363200 ⟨⟨112800922933, 112800922941⟩, ⟨109446917363, 116192359893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 237240320 365363200 368148480 ⟨⟨114596264176, 114596264182⟩, ⟨111221450776, 118008726514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 237240320 368148480 370933760 ⟨⟨115420173647, 115420173653⟩, ⟨112038543512, 118839483424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 238551040 365363200 368148480 ⟨⟨113619091472, 113619091479⟩, ⟨110258288561, 117017357489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237240320 238551040 368148480 370933760 ⟨⟨114436716617, 114436716624⟩, ⟨111069118590, 117841809274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239861760 359792640 362577920 ⟨⟨111021516446, 111021516450⟩, ⟨107688168652, 114392078017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238551040 239861760 362577920 365363200 ⟨⟨111833928663, 111833928668⟩, ⟨108493803508, 115211300295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 241172480 359792640 362577920 ⟨⟨110064648157, 110064648163⟩, ⟨106745051369, 113421274756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 241172480 362577920 365363200 ⟨⟨110870765557, 110870765564⟩, ⟨107544413872, 114234180526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 365363200 368148480 ⟨⟨112645807450, 112645807455⟩, ⟨109298907001, 116029986887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238551040 239861760 368148480 370933760 ⟨⟨113457155538, 113457155543⟩, ⟨110103481848, 116848140544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 241172480 365363200 368148480 ⟨⟨111676362078, 111676362084⟩, ⟨108343257391, 115046563340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 368148480 370933760 ⟨⟨112481440375, 112481440382⟩, ⟨109141584566, 115858425870⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 359792640 370933760 t = true :=
  ⟨_, (join_su (m := 238551040) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 362577920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 362577920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 237240320) (by decide) (join_sr (m := 368148480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 368148480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 365363200) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 362577920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 362577920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 239861760) (by decide) (join_sr (m := 368148480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 368148480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (549/1280 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((359792640 : ℤ) : ℝ) / (D : ℝ)) = (549/1280 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
