-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_71303168_r123535360_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:42:33.798651+00:00
-- url     : https://prove2.me/submissions/f42eb392-8aa6-48fa-aeee-a85535ae3b88

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 17/200]`, `ρ ∈ [377/2560, 207/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 68157440 123535360 126566400 ⟨⟨136385204996, 136385205009⟩, ⟨130246055806, 142656318807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 68157440 126566400 129597440 ⟨⟨139084010382, 139084010395⟩, ⟨132938034113, 145360825468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 68157440 69206016 123535360 126566400 ⟨⟨135044971145, 135044971156⟩, ⟨128971661615, 141247847683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 68157440 69206016 126566400 129597440 ⟨⟨137726232473, 137726232486⟩, ⟨131645837054, 143935112155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 68157440 129597440 132628480 ⟨⟨141761931393, 141761931404⟩, ⟨135609434187, 148044151770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 68157440 132628480 135659520 ⟨⟨144419355658, 144419355669⟩, ⟨138260633067, 150706695894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 68157440 69206016 129597440 132628480 ⟨⟨140387030735, 140387030746⟩, ⟨134299850345, 146601622089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 68157440 69206016 132628480 135659520 ⟨⟨143027741302, 143027741313⟩, ⟨136934066636, 149247763050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 69206016 70254592 123535360 126566400 ⟨⟨133728330373, 133728330383⟩, ⟨127719373359, 139864526168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 69206016 70254592 126566400 129597440 ⟨⟨136392155573, 136392155583⟩, ⟨130375869536, 142534638799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 70254592 71303168 123535360 126566400 ⟨⟨132434596498, 132434596511⟩, ⟨126488554912, 138505615332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 70254592 71303168 126566400 129597440 ⟨⟨135081095295, 135081095305⟩, ⟨129127496370, 141158669235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 69206016 70254592 129597440 132628480 ⟨⟨139035929377, 139035929390⟩, ⟨133012610009, 145184413140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 69206016 70254592 132628480 135659520 ⟨⟨141660015347, 141660015358⟩, ⟨135629948470, 147814222587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 70254592 71303168 129597440 132628480 ⟨⟨137707944984, 137707944994⟩, ⟨131747079180, 143791791747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 70254592 71303168 132628480 135659520 ⟨⟨140315497725, 140315497738⟩, ⟨134347645992, 146405344529⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 71303168 123535360 135659520 t = true :=
  ⟨_, (join_su (m := 69206016) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 68157440) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126566400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 68157440) (by decide) (join_sr (m := 132628480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 132628480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 129597440) (by decide) (join_su (m := 70254592) (by decide) (join_sr (m := 126566400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126566400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 70254592) (by decide) (join_sr (m := 132628480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 132628480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (17/200 : ℝ) →
    rho ∈ Set.Icc (377/2560 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e2 : (((123535360 : ℤ) : ℝ) / (D : ℝ)) = (377/2560 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
