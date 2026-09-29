-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r203816960_209387520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:23:15.818278+00:00
-- url     : https://prove2.me/submissions/886f47ec-019b-4dde-b837-454217edfee9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [311/1280, 639/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 203816960 205209600 ⟨⟨62214391604, 62214391607⟩, ⟨60758522687, 63678828768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 243793920 244449280 205209600 206602240 ⟨⟨62624715590, 62624715593⟩, ⟨61167145590, 64090859402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 244449280 245104640 203816960 205209600 ⟨⟨61929416694, 61929416700⟩, ⟨60476510191, 63390865065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 205209600 206602240 ⟨⟨62337975711, 62337975717⟩, ⟨60883372304, 63801126583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 244449280 206602240 207994880 ⟨⟨63034879266, 63034879268⟩, ⟨61575608454, 64502729448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243793920 244449280 207994880 209387520 ⟨⟨63444883005, 63444883007⟩, ⟨61983911652, 64914439277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 245104640 206602240 207994880 ⟨⟨62746376468, 62746376474⟩, ⟨61290076415, 64211229573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244449280 245104640 207994880 209387520 ⟨⟨63154619335, 63154619340⟩, ⟨61696622893, 64621174405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245760000 203816960 205209600 ⟨⟨61645138747, 61645138754⟩, ⟨60195181190, 63103611952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245104640 245760000 205209600 206602240 ⟨⟨62051935648, 62051935653⟩, ⟨60600285363, 63512107204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245760000 246415360 203816960 205209600 ⟨⟨61361552766, 61361552771⟩, ⟨59914530779, 62817064335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245760000 246415360 205209600 206602240 ⟨⟨61766590383, 61766590390⟩, ⟨60317879844, 63223796160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 206602240 207994880 ⟨⟨62458576318, 62458576323⟩, ⟨61005233551, 63920445972⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 245760000 207994880 209387520 ⟨⟨62865061121, 62865061126⟩, ⟨61410026115, 64328628620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246415360 206602240 207994880 ⟨⟨62171473782, 62171473789⟩, ⟨60721074922, 63630373523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 207994880 209387520 ⟨⟨62576203317, 62576203322⟩, ⟨61124116367, 64036796781⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 203816960 209387520 t = true :=
  ⟨_, (join_su (m := 245104640) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 205209600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 244449280) (by decide) (join_sr (m := 207994880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 207994880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 206602240) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 205209600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245760000) (by decide) (join_sr (m := 207994880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 207994880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (639/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((209387520 : ℤ) : ℝ) / (D : ℝ)) = (639/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
