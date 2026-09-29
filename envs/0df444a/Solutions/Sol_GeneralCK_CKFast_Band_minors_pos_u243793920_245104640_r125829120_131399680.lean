-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_245104640_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:25:35.21705+00:00
-- url     : https://prove2.me/submissions/43b9ddb9-92d8-4614-86f9-ea97e53fdde5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 187/640]`, `ρ ∈ [3/20, 401/2560]` by 19 cells of the computing
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
theorem cell0 : cellOK 243793920 244121600 125829120 127221760 ⟨⟨39014287747, 39014287752⟩, ⟨38216456146, 39815064484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244121600 244449280 125829120 126525440 ⟨⟨38817933770, 38817933776⟩, ⟨38137383642, 39500542242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 244121600 244449280 126525440 127221760 ⟨⟨39027702871, 39027702876⟩, ⟨38346723275, 39710741571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 243793920 244121600 127221760 128614400 ⟨⟨39434680786, 39434680792⟩, ⟨38635917648, 40236390532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 244121600 244449280 127221760 128614400 ⟨⟨39342271170, 39342271176⟩, ⟨38544485416, 40142997606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 244449280 244776960 125829120 126525440 ⟨⟨38726832493, 38726832498⟩, ⟨38046960497, 39408759363⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 244776960 126525440 127221760 ⟨⟨38936128873, 38936128878⟩, ⟨38255828027, 39618485353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244776960 245104640 125829120 126525440 ⟨⟨38635856534, 38635856536⟩, ⟨37956661031, 39317103448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 244776960 245104640 126525440 127221760 ⟨⟨38844680715, 38844680716⟩, ⟨38165056982, 39526356623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244449280 244776960 127221760 128614400 ⟨⟨39249988655, 39249988661⟩, ⟨38453178118, 40049733971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 244776960 245104640 127221760 128614400 ⟨⟨39157832762, 39157832765⟩, ⟨38361995282, 39956599130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 243793920 244121600 128614400 130007040 ⟨⟨39854890811, 39854890816⟩, ⟨39055196423, 40657533276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 244121600 244449280 128614400 130007040 ⟨⟨39761536520, 39761536526⟩, ⟨38962821014, 40563194183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243793920 244121600 130007040 131399680 ⟨⟨40274918240, 40274918245⟩, ⟨39474292887, 41078493132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 244121600 244449280 130007040 131399680 ⟨⟨40180620480, 40180620486⟩, ⟨39380975503, 40983209084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 244449280 244776960 128614400 130007040 ⟨⟨39668310371, 39668310376⟩, ⟨38870571575, 40468985421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 244776960 245104640 128614400 130007040 ⟨⟨39575211875, 39575211878⟩, ⟨38778447632, 40374906491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 244449280 244776960 130007040 131399680 ⟨⟨40086451894, 40086451899⟩, ⟨39287785118, 40888056400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 244776960 245104640 130007040 131399680 ⟨⟨39992411992, 39992411995⟩, ⟨39194721257, 40793034580⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 245104640 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell0) (join_sr (m := 126525440) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 244121600) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 127221760) (by decide) (join_su (m := 244776960) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 126525440) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 244776960) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_su (m := 244449280) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 244121600) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 244121600) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 130007040) (by decide) (join_su (m := 244776960) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 244776960) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (187/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
