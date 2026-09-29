-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u234618880_235929600_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:56:45.414391+00:00
-- url     : https://prove2.me/submissions/8133231e-5156-432c-9175-40f7cd5eb83e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [179/640, 9/32]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 234618880 234946560 148111360 149504000 ⟨⟨48759455904, 48759455911⟩, ⟨47917847077, 49604204763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 234946560 235274240 148111360 149504000 ⟨⟨48648800535, 48648800539⟩, ⟨47808255933, 49492478758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 234618880 234946560 149504000 150896640 ⟨⟨49203320087, 49203320093⟩, ⟨48360743640, 50049037819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 234946560 235274240 149504000 150896640 ⟨⟨49091710115, 49091710119⟩, ⟨48250199364, 49936355749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235274240 235601920 148111360 149504000 ⟨⟨48538302952, 48538302959⟩, ⟨47698820139, 49380913002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235601920 235929600 148111360 149504000 ⟨⟨48427962563, 48427962569⟩, ⟨47589539114, 49269506884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 235274240 235601920 149504000 150896640 ⟨⟨48980258961, 48980258967⟩, ⟨48139811468, 49823834960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235601920 235929600 149504000 150896640 ⟨⟨48868966028, 48868966033⟩, ⟨48029579367, 49711474836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 234618880 234946560 150896640 152289280 ⟨⟨49646972870, 49646972875⟩, ⟨48803429222, 50493659057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 234946560 235274240 150896640 152289280 ⟨⟨49534409636, 49534409640⟩, ⟨48691933149, 50380022266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 234946560 152289280 153681920 ⟨⟨50090414763, 50090414769⟩, ⟨49245904331, 50938068983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234946560 235274240 152289280 153681920 ⟨⟨49976899604, 49976899605⟩, ⟨49133457791, 50823478813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 235274240 235601920 150896640 152289280 ⟨⟨49422006244, 49422006249⟩, ⟨48580594478, 50266547781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235601920 235929600 150896640 152289280 ⟨⟨49309762092, 49309762098⟩, ⟨48469412620, 50153234985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 235274240 235601920 152289280 153681920 ⟨⟨49863545300, 49863545306⟩, ⟨49021169667, 50709051967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235601920 235929600 152289280 153681920 ⟨⟨49750351253, 49750351259⟩, ⟨48909039371, 50594787825⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 234618880 235929600 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 235274240) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 234946560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235601920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 235274240) (by decide) (join_sr (m := 152289280) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 234946560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 152289280) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235601920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (179/640 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
