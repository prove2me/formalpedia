-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u71303168_75497472_r111411200_123535360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:42:40.252583+00:00
-- url     : https://prove2.me/submissions/5e463e82-0e8a-4371-833a-f328a9c1e71b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/200, 9/100]`, `ρ ∈ [17/128, 377/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 71303168 72351744 111411200 114442240 ⟨⟨120446288859, 120446288872⟩, ⟨114595908361, 126423383455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 71303168 72351744 114442240 117473280 ⟨⟨123156182558, 123156182571⟩, ⟨117296790579, 129141293686⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 72351744 73400320 111411200 114442240 ⟨⟨119268894637, 119268894650⟩, ⟨113479442089, 125182775872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 72351744 73400320 114442240 117473280 ⟨⟨121960035378, 121960035391⟩, ⟨116161394625, 127882148118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 71303168 72351744 117473280 120504320 ⟨⟨125845367663, 125845367673⟩, ⟨119977289727, 131838177377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 71303168 72351744 120504320 123535360 ⟨⟨128514221100, 128514221112⟩, ⟨122637772100, 134514422105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 72351744 73400320 117473280 120504320 ⟨⟨124630897960, 124630897970⟩, ⟨118823387866, 130560930361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 72351744 73400320 120504320 123535360 ⟨⟨127281847151, 127281847164⟩, ⟨121465776343, 133219497629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 73400320 74448896 111411200 114442240 ⟨⟨118111956067, 118111956080⟩, ⟨112382082157, 123964039088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 73400320 74448896 114442240 117473280 ⟨⟨120784496418, 120784496430⟩, ⟨115045269858, 126645011959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 74448896 75497472 111411200 114442240 ⟨⟨116974886357, 116974886369⟩, ⟨111303286412, 122766539121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 74448896 75497472 114442240 117473280 ⟨⟨119628978747, 119628978759⟩, ⟨113947873288, 125429251873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 73400320 74448896 117473280 120504320 ⟨⟨123437178677, 123437178687⟩, ⟨117688911752, 129305820951⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 73400320 74448896 120504320 123535360 ⟨⟨126070355905, 126070355915⟩, ⟨120313351044, 131946829004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 74448896 75497472 117473280 120504320 ⟨⟨122263623037, 122263623047⟩, ⟨116573317861, 128072216739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 74448896 75497472 120504320 123535360 ⟨⟨124879161006, 124879161016⟩, ⟨119179952420, 130695785016⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 71303168 75497472 111411200 123535360 t = true :=
  ⟨_, (join_su (m := 73400320) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 72351744) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114442240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 72351744) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 120504320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 117473280) (by decide) (join_su (m := 74448896) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114442240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 74448896) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 120504320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/200 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (377/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
