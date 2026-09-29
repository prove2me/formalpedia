-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r348651520_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:17:24.688636+00:00
-- url     : https://prove2.me/submissions/1abaac00-30d0-4066-b331-d7caf9e15b33

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [133/320, 283/640]` by 19 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 348651520 354222080 ⟨⟨117738373266, 117738373268⟩, ⟨113711158669, 121820386590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226754560 228065280 348651520 354222080 ⟨⟨116763359390, 116763359396⟩, ⟨112756621322, 120824544107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 225443840 226754560 354222080 359792640 ⟨⟨119494019310, 119494019314⟩, ⟨115451814462, 123591048849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 354222080 359792640 ⟨⟨118506170363, 118506170370⟩, ⟨114484490287, 122582326058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228065280 229376000 348651520 351436800 ⟨⟨115359706737, 115359706743⟩, ⟨111940205387, 118817852573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 228065280 229376000 351436800 354222080 ⟨⟨116225358672, 116225358680⟩, ⟨112798894925, 119690493585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 229376000 230686720 348651520 351436800 ⟨⟨114396385489, 114396385496⟩, ⟨110991447654, 117839765635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229376000 230686720 351436800 354222080 ⟨⟨115255622105, 115255622111⟩, ⟨111843743040, 118705971077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 229376000 354222080 359792640 ⟨⟨117522607818, 117522607824⟩, ⟨113521293391, 121578052078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 229376000 230686720 354222080 357007360 ⟨⟨116114217600, 116114217608⟩, ⟨112695400768, 119571531719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 230686720 357007360 359792640 ⟨⟨116972175347, 116972175355⟩, ⟨113546424191, 120436450954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 225443840 226754560 359792640 365363200 ⟨⟨121246942163, 121246942167⟩, ⟨117189770621, 125358963226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226754560 228065280 359792640 365363200 ⟨⟨120246318801, 120246318807⟩, ⟨116209719236, 124337421844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 226754560 365363200 370933760 ⟨⟨122997170893, 122997170896⟩, ⟨118925055915, 127124159087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 226754560 228065280 365363200 370933760 ⟨⟨121983832985, 121983832993⟩, ⟨117932336166, 126089860029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 229376000 359792640 365363200 ⟨⟨119249997818, 119249997825⟩, ⟨115233811859, 123320344424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 229376000 230686720 359792640 365363200 ⟨⟨118257923530, 118257923538⟩, ⟨114261994790, 122307673264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 228065280 229376000 365363200 370933760 ⟨⟨120974812431, 120974812438⟩, ⟨116943776165, 125060039066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 229376000 230686720 365363200 370933760 ⟨⟨119970053562, 119970053570⟩, ⟨115959322208, 124034638533⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 348651520 370933760 t = true :=
  ⟨_, (join_sr (m := 359792640) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 226754560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 354222080) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 351436800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 351436800) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 229376000) (by decide) (leaf_ok cell8) (join_sr (m := 357007360) (by decide) (leaf_ok cell9) (leaf_ok cell10))))) (join_su (m := 228065280) (by decide) (join_sr (m := 365363200) (by decide) (join_su (m := 226754560) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 226754560) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 365363200) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 229376000) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
