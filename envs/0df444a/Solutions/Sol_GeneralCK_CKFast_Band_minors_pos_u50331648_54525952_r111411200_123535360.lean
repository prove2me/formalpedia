-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_54525952_r111411200_123535360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:07:24.564707+00:00
-- url     : https://prove2.me/submissions/0279a8a8-b7df-4df0-9fcf-301c4b21e3fa

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 13/200]`, `ρ ∈ [17/128, 377/2560]` by 15 cells of the computing
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
theorem cell0 : cellOK 50331648 51380224 111411200 114442240 ⟨⟨149458408120, 149458408136⟩, ⟨142014107044, 157094412908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 51380224 114442240 117473280 ⟨⟨152573387317, 152573387329⟩, ⟨145127816913, 160208341777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 51380224 52428800 111411200 114442240 ⟨⟨147699769107, 147699769122⟩, ⟨140357081145, 155229738036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 51380224 52428800 114442240 117473280 ⟨⟨150793347477, 150793347490⟩, ⟨143448715883, 158323044296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 51380224 117473280 123535360 ⟨⟨157186048954, 157186048970⟩, ⟨147049656391, 167664207828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 51380224 52428800 117473280 120504320 ⟨⟨153855615450, 153855615466⟩, ⟨146509492981, 161384618915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 51380224 52428800 120504320 123535360 ⟨⟨156887299747, 156887299760⟩, ⟨149540117251, 164415210096⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 52428800 53477376 111411200 114442240 ⟨⟨145980696399, 145980696414⟩, ⟨138736719742, 153407691862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 52428800 53477376 114442240 117473280 ⟨⟨149052958587, 149052958599⟩, ⟨141806406901, 156480411660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 53477376 54525952 111411200 114442240 ⟨⟨144299747024, 144299747039⟩, ⟨137151702763, 151626700721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 53477376 54525952 114442240 117473280 ⟨⟨147350786947, 147350786959⟩, ⟨140199576361, 154678882640⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 52428800 53477376 117473280 120504320 ⟨⟨152094605205, 152094605221⟩, ⟨144845925763, 159522097833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 52428800 53477376 120504320 123535360 ⟨⟨155106337092, 155106337105⟩, ⟨147855956066, 162533471942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 53477376 54525952 117473280 120504320 ⟨⟨150371888521, 150371888537⟩, ⟨143217953063, 157700711853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 53477376 54525952 120504320 123535360 ⟨⟨153363727760, 153363727773⟩, ⟨146207488560, 160692884368⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 54525952 111411200 123535360 t = true :=
  ⟨_, (join_su (m := 52428800) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 51380224) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114442240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 51380224) (by decide) (leaf_ok cell4) (join_sr (m := 120504320) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 117473280) (by decide) (join_su (m := 53477376) (by decide) (join_sr (m := 114442240) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 114442240) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 53477376) (by decide) (join_sr (m := 120504320) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 120504320) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (13/200 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (377/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((54525952 : ℤ) : ℝ) / (D : ℝ)) = (13/200 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
