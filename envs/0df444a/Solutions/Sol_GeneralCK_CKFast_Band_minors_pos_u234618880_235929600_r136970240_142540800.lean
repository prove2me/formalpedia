-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u234618880_235929600_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:29:07.694644+00:00
-- url     : https://prove2.me/submissions/1b726632-66bf-4f6d-8562-a54d310bca64

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [179/640, 9/32]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 234618880 234946560 136970240 138362880 ⟨⟨45200870756, 45200870761⟩, ⟨44367018061, 46037853295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 234946560 235274240 136970240 138362880 ⟨⟨45097900936, 45097900940⟩, ⟨44265100499, 45933824754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 234618880 234946560 138362880 139755520 ⟨⟨45646444554, 45646444559⟩, ⟨44811620856, 46484399381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 234946560 235274240 138362880 139755520 ⟨⟨45542509265, 45542509266⟩, ⟨44708739339, 46379403862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235274240 235601920 136970240 138362880 ⟨⟨44995080401, 44995080406⟩, ⟨44163329798, 45829947947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235601920 235929600 136970240 138362880 ⟨⟨44892408583, 44892408588⟩, ⟨44061705404, 45726222290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 235274240 235601920 138362880 139755520 ⟨⟨45438724346, 45438724351⟩, ⟨44606005770, 46274561166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235601920 235929600 138362880 139755520 ⟨⟨45335089232, 45335089237⟩, ⟨44503419591, 46169870704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 234618880 234946560 139755520 141148160 ⟨⟨46091802847, 46091802854⟩, ⟨45256008573, 46930729534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 234946560 235274240 139755520 141148160 ⟨⟨45986903460, 45986903464⟩, ⟨45152164470, 46824768414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 234618880 234946560 141148160 142540800 ⟨⟨46536946154, 46536946160⟩, ⟨45700181730, 47376844269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 234946560 235274240 141148160 142540800 ⟨⟨46431084039, 46431084043⟩, ⟨45595376403, 47269918923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 235274240 235601920 139755520 141148160 ⟨⟨45882155526, 45882155532⟩, ⟨45048469393, 46718961199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235601920 235929600 139755520 141148160 ⟨⟨45777558472, 45777558477⟩, ⟨44944922781, 46613307299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 235274240 235601920 141148160 142540800 ⟨⟨46325374450, 46325374456⟩, ⟨45490721173, 47163148558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235601920 235929600 141148160 142540800 ⟨⟨46219816811, 46219816817⟩, ⟨45386215478, 47056532578⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 234618880 235929600 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 235274240) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 234946560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235601920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 235274240) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 234946560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 234946560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 235601920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235601920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (179/640 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((234618880 : ℤ) : ℝ) / (D : ℝ)) = (179/640 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
