-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_235929600_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:10:47.554554+00:00
-- url     : https://prove2.me/submissions/cf4cdeba-888c-4521-8c94-c9d29f5ad1f4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 9/32]`, `ρ ∈ [43/128, 447/1280]` by 17 cells of the computing
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
theorem cell0 : cellOK 230686720 231997440 281804800 284590080 ⟨⟨92772580768, 92772580774⟩, ⟨89549196956, 96033460237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231997440 284590080 287375360 ⟨⟨93641464994, 93641465000⟩, ⟨90411076718, 96909382407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 233308160 281804800 284590080 ⟨⟨91975593653, 91975593656⟩, ⟨88765955206, 95222509880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231997440 233308160 284590080 287375360 ⟨⟨92837708618, 92837708621⟩, ⟨89621092518, 96091636744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231997440 287375360 290160640 ⟨⟨94509640127, 94509640134⟩, ⟨91272251166, 97784591503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231997440 290160640 292945920 ⟨⟨95377109762, 95377109767⟩, ⟨92132723871, 98659091139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 233308160 287375360 290160640 ⟨⟨93699131106, 93699131107⟩, ⟨90475540904, 96960067379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231997440 233308160 290160640 292945920 ⟨⟨94559864604, 94559864607⟩, ⟨91329303832, 97827805293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 234618880 281804800 284590080 ⟨⟨91182364175, 91182364181⟩, ⟨87986351056, 94415439627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233308160 234618880 284590080 287375360 ⟨⟨92037725213, 92037725220⟩, ⟨88834761403, 95277786348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 235274240 281804800 284590080 ⟨⟨90589877176, 90589877182⟩, ⟨88727867640, 92464850938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 235274240 235929600 281804800 284590080 ⟨⟨90196033544, 90196033552⟩, ⟨88338733990, 92066252253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 234618880 235929600 284590080 287375360 ⟨⟨91241463453, 91241463460⟩, ⟨88052033636, 94467778250⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 233308160 234618880 287375360 290160640 ⟨⟨92892410084, 92892410091⟩, ⟨89682498913, 96139453372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 233308160 234618880 290160640 292945920 ⟨⟨93746422175, 93746422181⟩, ⟨90529566955, 97000444110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 234618880 235929600 287375360 290160640 ⟨⟨92089425633, 92089425640⟩, ⟨88893075349, 95322696422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 234618880 235929600 290160640 292945920 ⟨⟨92936730946, 92936730952⟩, ⟨89733463289, 96176954439⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 235929600 281804800 292945920 t = true :=
  ⟨_, (join_su (m := 233308160) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 284590080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231997440) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 290160640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 287375360) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 284590080) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 234618880) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 290160640) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
