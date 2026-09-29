-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r209387520_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:20:08.492644+00:00
-- url     : https://prove2.me/submissions/d0e49fdb-05f6-48ef-a841-80d498abf801

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [639/2560, 41/160]` by 11 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 209387520 212172800 ⟨⟨65238393169, 65238393175⟩, ⟨63518040072, 66971030838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241827840 242483200 209387520 210780160 ⟨⟨64735095319, 64735095326⟩, ⟨63263404762, 66215456096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241827840 242483200 210780160 212172800 ⟨⟨65150067473, 65150067480⟩, ⟨63676664524, 66632146081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241172480 241827840 212172800 214958080 ⟨⟨66071539358, 66071539364⟩, ⟨64347490506, 67807882667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241827840 242483200 212172800 214958080 ⟨⟨65772216403, 65772216408⟩, ⟨64052463921, 67504217748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 242483200 243138560 209387520 210780160 ⟨⟨64440917346, 64440917352⟩, ⟨62972246825, 65918231337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243138560 210780160 212172800 ⟨⟨64854124301, 64854124307⟩, ⟨63383745519, 66333152023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243138560 243793920 209387520 210780160 ⟨⟨64147463024, 64147463030⟩, ⟨62681798784, 65621744151⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243138560 243793920 210780160 212172800 ⟨⟨64558907594, 64558907601⟩, ⟨63091539222, 66034898353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243138560 212172800 214958080 ⟨⟨65473629348, 65473629355⟩, ⟨63758155004, 67201307231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243138560 243793920 212172800 214958080 ⟨⟨65175772942, 65175772947⟩, ⟨63464558632, 66899145734⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 209387520 214958080 t = true :=
  ⟨_, (join_su (m := 242483200) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell0) (join_sr (m := 210780160) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 241827840) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 212172800) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 210780160) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 210780160) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 243138560) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (639/2560 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((209387520 : ℤ) : ℝ) / (D : ℝ)) = (639/2560 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
