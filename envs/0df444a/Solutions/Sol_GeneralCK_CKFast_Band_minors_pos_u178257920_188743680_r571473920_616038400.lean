-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_188743680_r571473920_616038400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:11.441212+00:00
-- url     : https://prove2.me/submissions/462e39df-efaa-42a3-b329-a42ebdb42d14

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 9/40]`, `ρ ∈ [109/160, 47/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 178257920 180879360 571473920 582615040 ⟨⟨241776308659, 241776308667⟩, ⟨230887325645, 252916450381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 180879360 183500800 571473920 582615040 ⟨⟨238496508048, 238496508058⟩, ⟨227713714593, 249528667902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 180879360 582615040 593756160 ⟨⟨245860210004, 245860210012⟩, ⟨234915849033, 257054084337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 180879360 183500800 582615040 593756160 ⟨⟨242539492870, 242539492879⟩, ⟨231700974932, 253625839592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 186122240 571473920 582615040 ⟨⟨235242306795, 235242306805⟩, ⟨224564377607, 246167808935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 186122240 188743680 571473920 582615040 ⟨⟨232013109791, 232013109800⟩, ⟨221438746843, 242833251948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 183500800 186122240 582615040 593756160 ⟨⟨239244157057, 239244157067⟩, ⟨228510193021, 250224260767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 186122240 188743680 582615040 593756160 ⟨⟨235973616742, 235973616750⟩, ⟨225342943470, 246848736975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 180879360 593756160 604897280 ⟨⟨249931271081, 249931271091⟩, ⟨238931826976, 261178560246⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 180879360 183500800 593756160 604897280 ⟨⟨246570052439, 246570052449⟩, ⟨235676093140, 257710279687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 178257920 180879360 604897280 616038400 ⟨⟨253989869743, 253989869754⟩, ⟨242935626917, 265290266274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 180879360 183500800 604897280 616038400 ⟨⟨250588549776, 250588549785⟩, ⟨239639422331, 261782361025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 183500800 186122240 593756160 604897280 ⟨⟨243233988711, 243233988721⟩, ⟨232444261191, 254268399224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 186122240 188743680 593756160 604897280 ⟨⟨239922503359, 239922503369⟩, ⟨229235779340, 250852318581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 183500800 186122240 604897280 616038400 ⟨⟨247212150407, 247212150417⟩, ⟨236366921347, 258300582287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 186122240 188743680 604897280 616038400 ⟨⟨243860104373, 243860104382⟩, ⟨233117580233, 254844340356⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 188743680 571473920 616038400 t = true :=
  ⟨_, (join_sr (m := 593756160) (by decide) (join_su (m := 183500800) (by decide) (join_sr (m := 582615040) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 180879360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 582615040) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 186122240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 183500800) (by decide) (join_sr (m := 604897280) (by decide) (join_su (m := 180879360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 180879360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 604897280) (by decide) (join_su (m := 186122240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 186122240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (9/40 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (47/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
