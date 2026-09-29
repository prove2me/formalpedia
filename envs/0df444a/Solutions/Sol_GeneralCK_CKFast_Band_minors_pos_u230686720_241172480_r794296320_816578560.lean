-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_241172480_r794296320_816578560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:15:24.587471+00:00
-- url     : https://prove2.me/submissions/778f8835-68b7-4ca1-83ac-6410724198c6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 23/80]`, `ρ ∈ [303/320, 623/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 233308160 794296320 799866880 ⟨⟨243325704887, 243325704896⟩, ⟨234436073977, 252374789741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 233308160 799866880 805437440 ⟨⟨244896247586, 244896247595⟩, ⟨235980020469, 253971849808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 235929600 794296320 799866880 ⟨⟨239633471067, 239633471076⟩, ⟨230807077907, 248619255142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233308160 235929600 799866880 805437440 ⟨⟨241183946226, 241183946235⟩, ⟨232330969355, 250196258892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 233308160 805437440 811008000 ⟨⟨246465962374, 246465962383⟩, ⟨237523139171, 255568077254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 233308160 811008000 816578560 ⟨⟨248034865878, 248034865887⟩, ⟨239065446419, 257163488970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 235929600 805437440 811008000 ⟨⟨242733625925, 242733625934⟩, ⟨233854064210, 251772463851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 233308160 235929600 811008000 816578560 ⟨⟨244282526082, 244282526091⟩, ⟨235376378114, 253347886184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 238551040 794296320 799866880 ⟨⟨235954554247, 235954554256⟩, ⟨227191064081, 244877352650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 235929600 238551040 799866880 805437440 ⟨⟨237484867830, 237484867841⟩, ⟨228694815335, 246434196601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 241172480 794296320 799866880 ⟨⟨232288678267, 232288678276⟩, ⟨223587760624, 241148802354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 238551040 241172480 799866880 805437440 ⟨⟨233798738656, 233798738665⟩, ⟨225071288770, 242685385625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 235929600 238551040 805437440 811008000 ⟨⟨239014417647, 239014417656⟩, ⟨230197800458, 247990274809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235929600 238551040 811008000 816578560 ⟨⟨240543218923, 240543218932⟩, ⟨231700034413, 249545602737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 238551040 241172480 805437440 811008000 ⟨⟨235308066209, 235308066219⟩, ⟨226554080508, 244221235419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 238551040 241172480 811008000 816578560 ⟨⟨236816675486, 236816675495⟩, ⟨228036150152, 245756366515⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 241172480 794296320 816578560 t = true :=
  ⟨_, (join_su (m := 235929600) (by decide) (join_sr (m := 805437440) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 799866880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 799866880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 233308160) (by decide) (join_sr (m := 811008000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 811008000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 805437440) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 799866880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 799866880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 238551040) (by decide) (join_sr (m := 811008000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 811008000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (303/320 : ℝ) (623/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  have e3 : (((816578560 : ℤ) : ℝ) / (D : ℝ)) = (623/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
