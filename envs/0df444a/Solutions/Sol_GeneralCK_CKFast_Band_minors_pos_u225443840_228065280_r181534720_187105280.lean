-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_228065280_r181534720_187105280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:54:20.464249+00:00
-- url     : https://prove2.me/submissions/adc5dcd0-e006-4553-a10e-0e8e4b9d1e3f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 87/320]`, `ρ ∈ [277/1280, 571/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 225443840 226099200 181534720 182927360 ⟨⟨63091417520, 63091417525⟩, ⟨61575923588, 64616214182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 225443840 226099200 182927360 184320000 ⟨⟨63556094454, 63556094460⟩, ⟨62038770290, 65082726119⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226099200 226754560 181534720 182927360 ⟨⟨62814730520, 62814730526⟩, ⟨61302547766, 64336183889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 226099200 226754560 182927360 184320000 ⟨⟨63277511437, 63277511443⟩, ⟨61763502954, 64800795344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 225443840 226099200 184320000 185712640 ⟨⟨64020535036, 64020535042⟩, ⟨62501381382, 65549000947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 225443840 226099200 185712640 187105280 ⟨⟨64484739864, 64484739869⟩, ⟨62963757457, 66015039269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226099200 226754560 184320000 185712640 ⟨⟨63740058856, 63740058863⟩, ⟨62224225368, 65265172567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 226099200 226754560 185712640 187105280 ⟨⟨64202373368, 64202373374⟩, ⟨62684715594, 65729316149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 226754560 227409920 181534720 182927360 ⟨⟨62538840803, 62538840809⟩, ⟨61029952788, 64056967528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226754560 227409920 182927360 184320000 ⟨⟨62999729457, 62999729463⟩, ⟨61489020217, 64519682259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 227409920 228065280 181534720 182927360 ⟨⟨62263742439, 62263742442⟩, ⟨60758132850, 63778559039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 227409920 228065280 182927360 184320000 ⟨⟨62722742564, 62722742567⟩, ⟨61215316249, 64239380784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 226754560 227409920 184320000 185712640 ⟨⟨63460387441, 63460387448⟩, ⟨61947857678, 64982165604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 226754560 227409920 185712640 187105280 ⟨⟨63920815336, 63920815342⟩, ⟨62406465751, 65444418146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 227409920 228065280 184320000 185712640 ⟨⟨63181514819, 63181514822⟩, ⟨61672272461, 64699973960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 227409920 228065280 185712640 187105280 ⟨⟨63640059774, 63640059777⟩, ⟨62129002055, 65160339143⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 228065280 181534720 187105280 t = true :=
  ⟨_, (join_su (m := 226754560) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 226099200) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 182927360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 226099200) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 185712640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184320000) (by decide) (join_su (m := 227409920) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 182927360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 227409920) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 185712640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (571/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
