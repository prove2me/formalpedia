-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r337510400_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:12:25.87671+00:00
-- url     : https://prove2.me/submissions/37078e63-67b1-4ee2-862f-7ac3886ade6f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [103/256, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 337510400 340295680 ⟨⟨113778060892, 113778060895⟩, ⟨110357129167, 117237946111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 225443840 226754560 340295680 343080960 ⟨⟨114659351767, 114659351771⟩, ⟨111231399520, 118126283197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226754560 228065280 337510400 340295680 ⟨⟨112832151824, 112832151832⟩, ⟨109425939805, 116277107324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 340295680 343080960 ⟨⟨113706947611, 113706947619⟩, ⟨110293736537, 117158928800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 225443840 226754560 343080960 345866240 ⟨⟨115539941572, 115539941574⟩, ⟨112104973003, 119013914784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225443840 226754560 345866240 348651520 ⟨⟨116419834024, 116419834027⟩, ⟨112977853305, 119900844617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 228065280 343080960 345866240 ⟨⟨114581058042, 114581058049⟩, ⟨111160851891, 118040060715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 226754560 228065280 345866240 348651520 ⟨⟨115454486733, 115454486741⟩, ⟨112027289462, 118920506713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 229376000 337510400 340295680 ⟨⟨111890470053, 111890470060⟩, ⟨108498855472, 115320620217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228065280 229376000 340295680 343080960 ⟨⟨112758780575, 112758780582⟩, ⟨109360188678, 116195935610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 230686720 337510400 340295680 ⟨⟨110952959959, 110952959966⟩, ⟨107575822130, 114368427569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229376000 230686720 340295680 343080960 ⟨⟨111814795020, 111814795027⟩, ⟨108430701882, 115237246393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 343080960 345866240 ⟨⟨113626421187, 113626421193⟩, ⟨110220855739, 117070577108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 228065280 229376000 345866240 348651520 ⟨⟨114493395405, 114493395412⟩, ⟨111080860148, 117944548253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230686720 343080960 345866240 ⟨⟨112675975350, 112675975356⟩, ⟨109284930456, 116105406718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 345866240 348651520 ⟨⟨113536504369, 113536504376⟩, ⟨110138511251, 116972911989⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 337510400 348651520 t = true :=
  ⟨_, (join_su (m := 228065280) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 340295680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 226754560) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 345866240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 343080960) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 340295680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 229376000) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 345866240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (103/256 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
