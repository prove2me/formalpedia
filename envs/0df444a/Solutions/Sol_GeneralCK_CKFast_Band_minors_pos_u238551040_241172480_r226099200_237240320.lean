-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:37:43.437184+00:00
-- url     : https://prove2.me/submissions/8deac4d8-dca4-468d-9863-c3c33cf35721

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 226099200 228884480 ⟨⟨71502504943, 71502504950⟩, ⟨69742445536, 73275090297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 239206400 239861760 226099200 228884480 ⟨⟨71182542279, 71182542286⟩, ⟨69426901959, 72950662425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 239206400 228884480 231669760 ⟨⟨72345681226, 72345681232⟩, ⟨70581901042, 74121996462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 228884480 231669760 ⟨⟨72022215695, 72022215701⟩, ⟨70262864089, 73794056353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239861760 240517120 226099200 228884480 ⟨⟨70863364321, 70863364328⟩, ⟨69112124339, 72627038281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240517120 241172480 226099200 228884480 ⟨⟨70544965516, 70544965519⟩, ⟨68798107247, 72304212177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239861760 240517120 228884480 231669760 ⟨⟨71699540096, 71699540103⟩, ⟨69944598317, 73466925191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240517120 241172480 228884480 231669760 ⟨⟨71377648848, 71377648851⟩, ⟨69627098278, 73140597264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239206400 231669760 234455040 ⟨⟨73188176740, 73188176746⟩, ⟨71420678169, 74968219416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239206400 239861760 231669760 234455040 ⟨⟨72861216790, 72861216795⟩, ⟨71098156214, 74636775585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 239206400 234455040 237240320 ⟨⟨74029994759, 74029994766⟩, ⟨72258780174, 75813762445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239206400 239861760 234455040 237240320 ⟨⟨73699548783, 73699548790⟩, ⟨71932781543, 75478823357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239861760 240517120 231669760 234455040 ⟨⟨72535051912, 72535051917⟩, ⟨70776410587, 74306145839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240517120 241172480 231669760 234455040 ⟨⟨72209676501, 72209676503⟩, ⟨70455435811, 73976324436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 240517120 234455040 237240320 ⟨⟨73369902940, 73369902945⟩, ⟨71607564306, 75144703406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240517120 241172480 234455040 237240320 ⟨⟨73041051598, 73041051601⟩, ⟨71283122958, 74811396828⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 239206400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240517120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239861760) (by decide) (join_sr (m := 234455040) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 239206400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 234455040) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240517120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
