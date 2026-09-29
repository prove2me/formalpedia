-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_204472320_r281804800_292945920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:33:58.295528+00:00
-- url     : https://prove2.me/submissions/ebc62324-e88c-4fd9-a0e0-95ec8f8df5d3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 39/160]`, `ρ ∈ [43/128, 447/1280]` by 15 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 281804800 284590080 ⟨⟨113175527052, 113175527055⟩, ⟨109581494920, 116813115418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 200540160 284590080 287375360 ⟨⟨114211734524, 114211734528⟩, ⟨110610120100, 117856912784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 200540160 201850880 281804800 284590080 ⟨⟨112270740964, 112270740970⟩, ⟨108693903743, 115890845804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 200540160 201850880 284590080 287375360 ⟨⟨113299781944, 113299781952⟩, ⟨109715383126, 116927457415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 200540160 287375360 292945920 ⟨⟨115763775282, 115763775285⟩, ⟨111466804204, 120123846126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 200540160 201850880 287375360 290160640 ⟨⟨114327636302, 114327636310⟩, ⟨110735686393, 117962871576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 200540160 201850880 290160640 292945920 ⟨⟨115354310905, 115354310913⟩, ⟨111754820344, 118997095222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201850880 203161600 281804800 284590080 ⟨⟨111371213057, 111371213063⟩, ⟨107811401704, 114974006925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 201850880 203161600 284590080 287375360 ⟨⟨112393105058, 112393105066⟩, ⟨108825753178, 116003449879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 203161600 204472320 281804800 284590080 ⟨⟨110476868419, 110476868427⟩, ⟨106933916415, 114062521292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203161600 204472320 284590080 287375360 ⟨⟨111491628888, 111491628895⟩, ⟨107941157792, 115084812637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 201850880 203161600 287375360 290160640 ⟨⟨113413835463, 113413835471⟩, ⟨109838953204, 117031720774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 201850880 203161600 290160640 292945920 ⟨⟨114433410954, 114433410960⟩, ⟨110851008397, 118058826358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203161600 204472320 287375360 290160640 ⟨⟨112505252357, 112505252365⟩, ⟨108947271963, 116105956878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203161600 204472320 290160640 292945920 ⟨⟨113517745327, 113517745335⟩, ⟨109952265367, 117125960579⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 204472320 281804800 292945920 t = true :=
  ⟨_, (join_su (m := 201850880) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 284590080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 200540160) (by decide) (leaf_ok cell4) (join_sr (m := 290160640) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 287375360) (by decide) (join_su (m := 203161600) (by decide) (join_sr (m := 284590080) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 284590080) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 203161600) (by decide) (join_sr (m := 290160640) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 290160640) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (447/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
