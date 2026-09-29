-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:57:25.771717+00:00
-- url     : https://prove2.me/submissions/d316f5f3-18dd-49bd-a2bc-40e787182473

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 248381440 251166720 ⟨⟨76842950815, 76842950822⟩, ⟨75071051903, 78627267842⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241827840 242483200 248381440 251166720 ⟨⟨76498461491, 76498461496⟩, ⟨74730981604, 78278315339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241827840 251166720 253952000 ⟨⟨77667052512, 77667052517⟩, ⟨75891487385, 79455044892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 251166720 253952000 ⟨⟨77319144696, 77319144703⟩, ⟨75548007578, 79102665032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 242483200 243138560 248381440 251166720 ⟨⟨76154773653, 76154773659⟩, ⟨74391694593, 77930182769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243138560 243793920 248381440 251166720 ⟨⟨75811881724, 75811881730⟩, ⟨74053185414, 77582864430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243138560 251166720 253952000 ⟨⟨76972042867, 76972042872⟩, ⟨75205315563, 78751109593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243138560 243793920 251166720 253952000 ⟨⟨76625741421, 76625741428⟩, ⟨74863405866, 78400372853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241827840 253952000 256737280 ⟨⟨78490531015, 78490531021⟩, ⟨76711301695, 80282196674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241827840 242483200 253952000 256737280 ⟨⟨78139212457, 78139212464⟩, ⟨76364420064, 79926397269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 241827840 256737280 259522560 ⟨⟨79313389311, 79313389317⟩, ⟨77530497806, 81108726188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 241827840 242483200 256737280 259522560 ⟨⟨78958667712, 78958667718⟩, ⟨77180221990, 80749515002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 242483200 243138560 253952000 256737280 ⟨⟨77788704306, 77788704312⟩, ⟨76018330656, 79571426697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243138560 243793920 253952000 256737280 ⟨⟨77439000940, 77439000947⟩, ⟨75673027975, 79217279212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 242483200 243138560 256737280 259522560 ⟨⟨78604760867, 78604760873⟩, ⟨76830742754, 80391136986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243138560 243793920 256737280 259522560 ⟨⟨78251663136, 78251663141⟩, ⟨76482054582, 80033586374⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 248381440 259522560 t = true :=
  ⟨_, (join_sr (m := 253952000) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 251166720) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241827840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 251166720) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243138560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 242483200) (by decide) (join_sr (m := 256737280) (by decide) (join_su (m := 241827840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 241827840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 256737280) (by decide) (join_su (m := 243138560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 243138560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
