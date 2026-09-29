-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u247726080_249036800_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:45:53.304979+00:00
-- url     : https://prove2.me/submissions/581ef991-25c3-41a8-876c-8c2f93767140

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [189/640, 19/64]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 247726080 248053760 131399680 132792320 ⟨⟨39560368898, 39560368904⟩, ⟨38770453518, 40353165615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 248053760 248381440 131399680 132792320 ⟨⟨39466659185, 39466659187⟩, ⟨38677700108, 40258493912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 248053760 132792320 134184960 ⟨⟨39968806119, 39968806123⟩, ⟨39177978013, 40762517076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 248053760 248381440 132792320 134184960 ⟨⟨39874167349, 39874167351⟩, ⟨39084297005, 40666914862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 248381440 248709120 131399680 132792320 ⟨⟨39373073888, 39373073894⟩, ⟨38585069034, 40163948729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248709120 249036800 131399680 132792320 ⟨⟨39279612543, 39279612549⟩, ⟨38492559841, 40069529584⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 248381440 248709120 132792320 134184960 ⟨⟨39779653975, 39779653981⟩, ⟨38990739312, 40571440149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248709120 249036800 132792320 134184960 ⟨⟨39685265530, 39685265535⟩, ⟨38897304474, 40476092453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248053760 134184960 135577600 ⟨⟨40377075923, 40377075930⟩, ⟨39585335323, 41171700889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 248053760 248381440 134184960 135577600 ⟨⟨40281509219, 40281509221⟩, ⟨39490727836, 41075169289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 247726080 248053760 135577600 136970240 ⟨⟨40785178690, 40785178695⟩, ⟨39992525825, 41580717431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248053760 248381440 135577600 136970240 ⟨⟨40688685167, 40688685170⟩, ⟨39896992969, 41483257566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 248381440 248709120 134184960 135577600 ⟨⟨40186068884, 40186068889⟩, ⟨39396244633, 40978766165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248709120 249036800 134184960 135577600 ⟨⟨40090754446, 40090754451⟩, ⟨39301885255, 40882491030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 248709120 135577600 136970240 ⟨⟨40592318981, 40592318986⟩, ⟨39801585365, 41385927147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248709120 249036800 135577600 136970240 ⟨⟨40496079657, 40496079662⟩, ⟨39706302547, 41288725683⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 247726080 249036800 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 248053760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 248709120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 248381440) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 248053760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 248053760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 248709120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 248709120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (189/640 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
