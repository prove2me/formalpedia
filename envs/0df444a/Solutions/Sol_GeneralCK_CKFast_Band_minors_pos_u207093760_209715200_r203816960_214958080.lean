-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u207093760_209715200_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:19:14.108606+00:00
-- url     : https://prove2.me/submissions/59965d88-c871-4bbf-a8c9-ce73c620dce8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [79/320, 1/4]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 207093760 207749120 203816960 206602240 ⟨⟨79716382723, 79716382729⟩, ⟨77752822570, 81695037976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 207749120 208404480 203816960 206602240 ⟨⟨79382045579, 79382045581⟩, ⟨77423910727, 81355211557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 207093760 207749120 206602240 209387520 ⟨⟨80744200144, 80744200150⟩, ⟨78776419170, 82727077780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 207749120 208404480 206602240 209387520 ⟨⟨80405967188, 80405967191⟩, ⟨78443621304, 82383345993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 208404480 209059840 203816960 206602240 ⟨⟨79048762652, 79048762658⟩, ⟨77096026180, 81016466716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209059840 209715200 203816960 206602240 ⟨⟨78716525982, 78716525988⟩, ⟨76769161176, 80678795272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 208404480 209059840 206602240 209387520 ⟨⟨80068796024, 80068796032⟩, ⟨78111858328, 82040703339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 209059840 209715200 206602240 209387520 ⟨⟨79732678659, 79732678666⟩, ⟨77781122454, 81699141598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 207749120 209387520 212172800 ⟨⟨81770764045, 81770764051⟩, ⟨79798769500, 83757856716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207749120 208404480 209387520 212172800 ⟨⟨81428649438, 81428649441⟩, ⟨79462099645, 83410233852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 207749120 212172800 214958080 ⟨⟨82796081401, 82796081409⟩, ⟨80819880494, 84787381811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207749120 208404480 212172800 214958080 ⟨⟨82450099204, 82450099207⟩, ⟨80479352580, 84435882057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 208404480 209059840 209387520 212172800 ⟨⟨81087604067, 81087604073⟩, ⟨79126472140, 83063707539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 209059840 209715200 209387520 212172800 ⟨⟨80747619897, 80747619904⟩, ⟨78791879162, 82718269522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209059840 212172800 214958080 ⟨⟨82105193549, 82105193556⟩, ⟨80139874346, 84085486137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 209059840 209715200 212172800 214958080 ⟨⟨81761356369, 81761356375⟩, ⟨79801437931, 83736185762⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 207093760 209715200 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 207749120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 209059840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 208404480) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 207749120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 209059840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (79/320 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
