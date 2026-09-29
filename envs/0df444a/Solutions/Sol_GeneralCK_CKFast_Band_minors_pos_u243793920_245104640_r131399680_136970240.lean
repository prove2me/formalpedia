-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_245104640_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:29:00.630038+00:00
-- url     : https://prove2.me/submissions/614cda95-9591-45f3-950e-9a471a03cce7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 187/640]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244121600 131399680 132792320 ⟨⟨40694763487, 40694763494⟩, ⟨39893207458, 41499270521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244121600 244449280 131399680 132792320 ⟨⟨40599523464, 40599523470⟩, ⟨39798949297, 41403042724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244121600 132792320 134184960 ⟨⟨41114426973, 41114426978⟩, ⟨40311940552, 41919865857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244121600 244449280 132792320 134184960 ⟨⟨41018245883, 41018245890⟩, ⟨40216742808, 41822695517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 244449280 244776960 131399680 132792320 ⟨⟨40504413637, 40504413644⟩, ⟨39704819159, 41306947320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 244776960 245104640 131399680 132792320 ⟨⟨40409433519, 40409433520⟩, ⟨39610816562, 41210983802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 244776960 132792320 134184960 ⟨⟨40922196011, 40922196016⟩, ⟨40121674104, 41725658589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244776960 245104640 132792320 134184960 ⟨⟨40826276860, 40826276863⟩, ⟨40026733956, 41628754567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244121600 134184960 135577600 ⟨⟨41533909111, 41533909116⟩, ⟨40730492584, 42340279558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244121600 244449280 134184960 135577600 ⟨⟨41436788151, 41436788158⟩, ⟨40634356447, 42242167874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244121600 135577600 136970240 ⟨⟨41953210316, 41953210322⟩, ⟨41148863966, 42760512039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244121600 244449280 135577600 136970240 ⟨⟨41855150679, 41855150685⟩, ⟨41051790626, 42661460210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 244449280 244776960 134184960 135577600 ⟨⟨41339799422, 41339799427⟩, ⟨40538350362, 42144190618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 244776960 245104640 134184960 135577600 ⟨⟨41242942423, 41242942426⟩, ⟨40442473841, 42046347278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 244449280 244776960 135577600 136970240 ⟨⟨41757224278, 41757224284⟩, ⟨40954848342, 42562543817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 244776960 245104640 135577600 136970240 ⟨⟨41659430611, 41659430614⟩, ⟨40858036622, 42463762343⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 245104640 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244121600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 244776960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 244449280) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244121600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 244776960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (187/640 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
