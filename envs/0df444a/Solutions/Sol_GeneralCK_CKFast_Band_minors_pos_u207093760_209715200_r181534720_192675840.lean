-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u207093760_209715200_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:16:49.868174+00:00
-- url     : https://prove2.me/submissions/33baba65-b913-4c3f-a216-d18994da1df3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [79/320, 1/4]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 207093760 207749120 181534720 184320000 ⟨⟨71447866668, 71447866675⟩, ⟨69518339865, 73392472626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 207749120 208404480 181534720 184320000 ⟨⟨71145218377, 71145218380⟩, ⟨69221033795, 73084416312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 207093760 207749120 184320000 187105280 ⟨⟨72485968065, 72485968073⟩, ⟨70552160706, 74434856910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 207749120 208404480 184320000 187105280 ⟨⟨72179306889, 72179306893⟩, ⟨70250852611, 74122777077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 208404480 209059840 181534720 184320000 ⟨⟨70843558653, 70843558660⟩, ⟨68924689279, 72777376046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209059840 209715200 181534720 184320000 ⟨⟨70542879879, 70542879886⟩, ⟨68629298912, 72471343983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 208404480 209059840 184320000 187105280 ⟨⟨71873642991, 71873642998⟩, ⟨69950514784, 73811721995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 209059840 209715200 184320000 187105280 ⟨⟨71568968705, 71568968713⟩, ⟨69651139778, 73501683768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 207749120 187105280 189890560 ⟨⟨73522758725, 73522758733⟩, ⟨71584678448, 75475922722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207749120 208404480 187105280 189890560 ⟨⟨73212099674, 73212099678⟩, ⟨71279383198, 75159834521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 207749120 189890560 192675840 ⟨⟨74558245940, 74558245946⟩, ⟨72615900330, 76515677406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207749120 208404480 189890560 192675840 ⟨⟨74243603916, 74243603917⟩, ⟨72306632692, 76195595872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 208404480 209059840 187105280 189890560 ⟨⟨72902446464, 72902446470⟩, ⟨70975066789, 74844779621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 209059840 209715200 187105280 189890560 ⟨⟨72593791384, 72593791390⟩, ⟨70671721722, 74530750082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209059840 189890560 192675840 ⟨⟨73929976148, 73929976154⟩, ⟨71998352320, 75876556044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 209059840 209715200 189890560 192675840 ⟨⟨73617354883, 73617354889⟩, ⟨71691051671, 75558549940⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 207093760 209715200 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 207749120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 209059840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 208404480) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 207749120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 209059840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (79/320 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
