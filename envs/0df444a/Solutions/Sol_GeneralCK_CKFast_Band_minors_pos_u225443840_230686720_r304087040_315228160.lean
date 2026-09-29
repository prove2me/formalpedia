-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_230686720_r304087040_315228160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:08:18.370984+00:00
-- url     : https://prove2.me/submissions/486b05a0-8dc5-4eee-8d9a-efba726a5f56

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 11/40]`, `ρ ∈ [29/80, 481/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226754560 304087040 306872320 ⟨⟨103146512601, 103146512605⟩, ⟨99810164205, 106521488497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 225443840 226754560 306872320 309657600 ⟨⟨104036511891, 104036511894⟩, ⟨100693090537, 107418589157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226754560 228065280 304087040 306872320 ⟨⟨102279808151, 102279808157⟩, ⟨98957904252, 105640118563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226754560 228065280 306872320 309657600 ⟨⟨103163115633, 103163115640⟩, ⟨99834162980, 106530504098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 225443840 226754560 309657600 312442880 ⟨⟨104925764304, 104925764307⟩, ⟨101575274506, 108314938199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225443840 226754560 312442880 315228160 ⟨⟨105814273740, 105814273743⟩, ⟨102456719987, 109210539551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 228065280 309657600 312442880 ⟨⟨104045693217, 104045693223⟩, ⟨100709696090, 107420155237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 226754560 228065280 312442880 315228160 ⟨⟨104927544698, 104927544704⟩, ⟨101584507351, 108309075796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 229376000 304087040 306872320 ⟨⟨101417191183, 101417191190⟩, ⟨98109606578, 104762963702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228065280 229376000 306872320 309657600 ⟨⟨102293820110, 102293820118⟩, ⟨98979211174, 105646647128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 230686720 304087040 306872320 ⟨⟨100558606628, 100558606634⟩, ⟨97265217784, 103889967145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229376000 230686720 306872320 309657600 ⟨⟨101428570187, 101428570193⟩, ⟨98128181646, 104766961409⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 309657600 312442880 ⟨⟨103169735820, 103169735827⟩, ⟨99848106603, 106529613070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 228065280 229376000 312442880 315228160 ⟨⟨104044942002, 104044942009⟩, ⟨100716296528, 107411865240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 229376000 230686720 309657600 312442880 ⟨⟨102297836913, 102297836919⟩, ⟨98990452501, 105643254808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229376000 230686720 312442880 315228160 ⟨⟨103166410392, 103166410398⟩, ⟨99852033908, 106518850945⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 230686720 304087040 315228160 t = true :=
  ⟨_, (join_su (m := 228065280) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 226754560) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 306872320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 226754560) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 312442880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 309657600) (by decide) (join_su (m := 229376000) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 306872320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 229376000) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 312442880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (481/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
