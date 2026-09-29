-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u186122240_188743680_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:38:29.093131+00:00
-- url     : https://prove2.me/submissions/7ba392e4-9033-4ef5-904a-0f19688142d2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [71/320, 9/40]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 186122240 186777600 181534720 184320000 ⟨⟨81704231344, 81704231350⟩, ⟨79588040103, 83837879100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 186777600 187432960 181534720 184320000 ⟨⟨81365452476, 81365452483⟩, ⟨79255599664, 83492678630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 186122240 186777600 184320000 187105280 ⟨⟨82875639606, 82875639613⟩, ⟨80754827950, 85013900732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 186777600 187432960 184320000 187105280 ⟨⟨82532542771, 82532542779⟩, ⟨80418079795, 84664372415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 187432960 188088320 181534720 184320000 ⟨⟨81027949196, 81027949203⟩, ⟨78924399326, 83148789871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188088320 188743680 181534720 184320000 ⟨⟨80691711083, 80691711086⟩, ⟨78594428982, 82806202076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 187432960 188088320 184320000 187105280 ⟨⟨82190731866, 82190731872⟩, ⟨80082582116, 84316166108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 188088320 188743680 184320000 187105280 ⟨⟨81850196414, 81850196418⟩, ⟨79748324750, 83969271012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 186122240 186777600 187105280 189890560 ⟨⟨84045170118, 84045170125⟩, ⟨81919751047, 86188031489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 186777600 187432960 187105280 189890560 ⟨⟨83697775858, 83697775864⟩, ⟨81578715517, 85834196062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 186122240 186777600 189890560 192675840 ⟨⟨85212834633, 85212834639⟩, ⟨83082821049, 87360283220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 186777600 187432960 189890560 192675840 ⟨⟨84861163310, 84861163317⟩, ⟨82737518313, 87002161246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 187432960 188088320 187105280 189890560 ⟨⟨83351677665, 83351677672⟩, ⟨81238940640, 85481692743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 188088320 188743680 187105280 189890560 ⟨⟨83006865015, 83006865018⟩, ⟨80900416200, 85130510682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 187432960 188088320 189890560 192675840 ⟨⟨84510798000, 84510798006⟩, ⟨82393486212, 86645381279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 188088320 188743680 189890560 192675840 ⟨⟨84161728126, 84161728128⟩, ⟨82050714476, 86289932422⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 186122240 188743680 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 187432960) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 186777600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 186777600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 188088320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 188088320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 187432960) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 186777600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 186777600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 188088320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 188088320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (71/320 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
