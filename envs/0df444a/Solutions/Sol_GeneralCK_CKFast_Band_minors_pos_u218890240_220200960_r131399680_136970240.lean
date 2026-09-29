-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u218890240_220200960_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:22:09.776112+00:00
-- url     : https://prove2.me/submissions/1e8a5fec-9014-4981-8c81-805c7864da22

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [167/640, 21/80]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 218890240 219217920 131399680 132792320 ⟨⟨48354788050, 48354788057⟩, ⟨47471576471, 49241463422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 219217920 219545600 131399680 132792320 ⟨⟨48248037913, 48248037919⟩, ⟨47366000197, 49133531757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 218890240 219217920 132792320 134184960 ⟨⟨48849226303, 48849226309⟩, ⟨47964965829, 49736951491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 219217920 219545600 132792320 134184960 ⟨⟨48741446967, 48741446972⟩, ⟨47858361988, 49627989003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 219545600 219873280 131399680 132792320 ⟨⟨48141462366, 48141462373⟩, ⟨47260595594, 49025777628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 219873280 220200960 131399680 132792320 ⟨⟨48035060722, 48035060729⟩, ⟨47155361987, 48918200337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 219545600 219873280 132792320 134184960 ⟨⟨48633843529, 48633843536⟩, ⟨47751931125, 49519205364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 219873280 220200960 132792320 134184960 ⟨⟨48526415299, 48526415305⟩, ⟨47645672560, 49410599867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 218890240 219217920 134184960 135577600 ⟨⟨49343370801, 49343370807⟩, ⟨48458062190, 50232145041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 219217920 219545600 134184960 135577600 ⟨⟨49234564058, 49234564063⟩, ⟨48350432568, 50122153531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 219217920 135577600 136970240 ⟨⟨49837222312, 49837222319⟩, ⟨48950866325, 50727044841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 219217920 219545600 135577600 136970240 ⟨⟨49727389947, 49727389953⟩, ⟨48842212696, 50616026102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 219545600 219873280 134184960 135577600 ⟨⟨49125934512, 49125934519⟩, ⟨48242977220, 50012342169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 219873280 220200960 134184960 135577600 ⟨⟨49017481469, 49017481474⟩, ⟨48135695462, 49902710248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 219545600 219873280 135577600 136970240 ⟨⟨49617736070, 49617736076⟩, ⟨48733734631, 50505188803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219873280 220200960 135577600 136970240 ⟨⟨49508259980, 49508259986⟩, ⟨48625431441, 50394532233⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 218890240 220200960 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 219545600) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 219217920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 219217920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 219873280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 219873280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 219545600) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 219217920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 219217920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 219873280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 219873280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (167/640 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((218890240 : ℤ) : ℝ) / (D : ℝ)) = (167/640 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
