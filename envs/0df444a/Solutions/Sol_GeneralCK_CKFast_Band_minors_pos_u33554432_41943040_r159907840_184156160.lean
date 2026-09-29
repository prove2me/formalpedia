-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:48:34.202542+00:00
-- url     : https://prove2.me/submissions/230e960f-8918-4666-94ac-9b40a825652e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 1/20]`, `ρ ∈ [61/320, 281/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 33554432 35651584 159907840 165969920 ⟨⟨234924148648, 234924148668⟩, ⟨216764782173, 253957417818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 33554432 35651584 165969920 172032000 ⟨⟨240567346821, 240567346841⟩, ⟨222485135197, 259495804174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 35651584 37748736 159907840 165969920 ⟨⟨229272954202, 229272954221⟩, ⟨211656579070, 247724110026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 35651584 37748736 165969920 172032000 ⟨⟨234882946229, 234882946245⟩, ⟨217332016923, 253243350105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 33554432 35651584 172032000 178094080 ⟨⟨246097752900, 246097752921⟩, ⟨228093068265, 264922165731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 33554432 35651584 178094080 184156160 ⟨⟨251520841626, 251520841646⟩, ⟨233593877054, 270242094633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 35651584 37748736 172032000 178094080 ⟨⟨240383680918, 240383680933⟩, ⟨222898873328, 258653650559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 35651584 37748736 178094080 184156160 ⟨⟨245780325523, 245780325542⟩, ⟨228362133683, 263960309477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 37748736 39845888 159907840 165969920 ⟨⟨223888027828, 223888027847⟩, ⟨206781763893, 241792596575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 37748736 39845888 165969920 172032000 ⟨⟨229461272531, 229461272549⟩, ⟨212410003119, 247287651614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 39845888 41943040 159907840 165969920 ⟨⟨218748830958, 218748830976⟩, ⟨202122764393, 236139146276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 39845888 41943040 165969920 172032000 ⟨⟨224282355770, 224282355789⟩, ⟨207701937883, 241605727493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 37748736 39845888 172032000 178094080 ⟨⟨234928763483, 234928763501⟩, ⟨217933408699, 252676900714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 37748736 39845888 178094080 184156160 ⟨⟨240295375966, 240295375984⟩, ⟨223356674144, 257965358681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 39845888 41943040 172032000 178094080 ⟨⟨229713580764, 229713580779⟩, ⟨213179926408, 246969653346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 39845888 41943040 178094080 184156160 ⟨⟨235047104697, 235047104712⟩, ⟨218561149210, 252235667128⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 41943040 159907840 184156160 t = true :=
  ⟨_, (join_su (m := 37748736) (by decide) (join_sr (m := 172032000) (by decide) (join_su (m := 35651584) (by decide) (join_sr (m := 165969920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 165969920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 35651584) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 178094080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 172032000) (by decide) (join_su (m := 39845888) (by decide) (join_sr (m := 165969920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 165969920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 39845888) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 178094080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
