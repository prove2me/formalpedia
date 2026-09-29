-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_217579520_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:34:05.708356+00:00
-- url     : https://prove2.me/submissions/aec360b3-a87f-4115-bedc-bcd39670abc6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 83/320]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 215613440 181534720 184320000 ⟨⟨67879690180, 67879690186⟩, ⟨66012533983, 69761165355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 215613440 216268800 181534720 184320000 ⟨⟨67588416761, 67588416768⟩, ⟨65726292546, 69464799394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 215613440 184320000 187105280 ⟨⟨68870201465, 68870201471⟩, ⟨66998895289, 70755831438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 215613440 216268800 184320000 187105280 ⟨⟨68575016586, 68575016593⟩, ⟨66708753288, 70455543312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 216268800 216924160 181534720 184320000 ⟨⟨67298044911, 67298044918⟩, ⟨65440928144, 69169359947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 216924160 217579520 181534720 184320000 ⟨⟨67008567801, 67008567807⟩, ⟨65156434138, 68874839988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 216924160 184320000 187105280 ⟨⟨68280741431, 68280741438⟩, ⟨66419496471, 70156189850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216924160 217579520 184320000 187105280 ⟨⟨67987369122, 67987369127⟩, ⟨66131118159, 69857763979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 215613440 187105280 189890560 ⟨⟨69859572717, 69859572724⟩, ⟨67984122651, 71749351313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 215613440 216268800 187105280 189890560 ⟨⟨69560489713, 69560489720⟩, ⟨67690093298, 71445154474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 215613440 189890560 192675840 ⟨⟨70847810020, 70847810025⟩, ⟨68968222115, 72741731100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 215613440 216268800 189890560 192675840 ⟨⟨70544842130, 70544842136⟩, ⟨68670318532, 72433638907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 216268800 216924160 187105280 189890560 ⟨⟨69262324452, 69262324459⟩, ⟨67396957153, 71141900316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 216924160 217579520 187105280 189890560 ⟨⟨68965070014, 68965070021⟩, ⟨67104707488, 70839581724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 216268800 216924160 189890560 192675840 ⟨⟨70242799875, 70242799880⟩, ⟨68373316051, 72126497283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 216924160 217579520 189890560 192675840 ⟨⟨69941676290, 69941676296⟩, ⟨68077207902, 71820299066⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 217579520 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 215613440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 215613440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 216924160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 216268800) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 215613440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 215613440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 216924160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (83/320 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
