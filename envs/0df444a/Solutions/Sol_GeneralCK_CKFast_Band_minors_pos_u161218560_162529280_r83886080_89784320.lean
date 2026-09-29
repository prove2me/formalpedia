-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u161218560_162529280_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:16:55.572476+00:00
-- url     : https://prove2.me/submissions/e1b59fc7-300f-42dd-b258-465102cf03eb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [123/640, 31/160]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 161218560 161546240 83886080 85360640 ⟨⟨46274993920, 46274993924⟩, ⟨45148974992, 47406770789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 161546240 161873920 83886080 85360640 ⟨⟨46171398735, 46171398741⟩, ⟨45047320336, 47301217009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 161218560 161546240 85360640 86835200 ⟨⟨47048293941, 47048293946⟩, ⟨45920682699, 48181660171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 161546240 161873920 85360640 86835200 ⟨⟨46943095782, 46943095790⟩, ⟨45817428010, 48074500521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 161873920 162201600 83886080 85360640 ⟨⟨46068079716, 46068079722⟩, ⟨44945935095, 47195946232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162201600 162529280 83886080 85360640 ⟨⟨45965035452, 45965035459⟩, ⟨44844817894, 47090957017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 161873920 162201600 85360640 86835200 ⟨⟨46838177324, 46838177332⟩, ⟨45714446266, 47967627417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 162201600 162529280 85360640 86835200 ⟨⟨46733537145, 46733537152⟩, ⟨45611736078, 47861039400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 161218560 161546240 86835200 88309760 ⟨⟨47820553774, 47820553778⟩, ⟨46691354891, 48955504674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 161546240 161873920 86835200 88309760 ⟨⟨47713758777, 47713758783⟩, ⟨46586506267, 48846745329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161218560 161546240 88309760 89784320 ⟨⟨48591777680, 48591777685⟩, ⟨47460995805, 49728308590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161546240 161873920 88309760 89784320 ⟨⟨48483391944, 48483391950⟩, ⟨47354559308, 49617955684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161873920 162201600 86835200 88309760 ⟨⟨47607246980, 47607246986⟩, ⟨46481934083, 48738276032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 162201600 162529280 86835200 88309760 ⟨⟨47501016946, 47501016952⟩, ⟨46377636935, 48630095313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161873920 162201600 88309760 89784320 ⟨⟨48375292871, 48375292878⟩, ⟨47248402711, 49507896295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 162201600 162529280 88309760 89784320 ⟨⟨48267479011, 48267479017⟩, ⟨47142524593, 49398128936⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 161218560 162529280 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 161873920) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 161546240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 161546240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 162201600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 162201600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 161873920) (by decide) (join_sr (m := 88309760) (by decide) (join_su (m := 161546240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 161546240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 88309760) (by decide) (join_su (m := 162201600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 162201600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (123/640 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((161218560 : ℤ) : ℝ) / (D : ℝ)) = (123/640 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
