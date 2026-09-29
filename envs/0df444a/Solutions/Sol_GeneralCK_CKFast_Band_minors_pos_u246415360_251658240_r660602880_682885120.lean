-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r660602880_682885120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:00:16.232549+00:00
-- url     : https://prove2.me/submissions/d8c211ad-e82f-4c24-9fd4-60aa4540dcd3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [63/80, 521/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 660602880 666173440 ⟨⟨187149131136, 187149131144⟩, ⟨182649885919, 191700290018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247726080 249036800 660602880 666173440 ⟨⟨185589682901, 185589682909⟩, ⟨181110835665, 190120281308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247726080 666173440 671744000 ⟨⟨188622639276, 188622639284⟩, ⟨184109560704, 193187647311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 666173440 671744000 ⟨⟨187052479675, 187052479684⟩, ⟨182559824465, 191596904885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 250347520 660602880 666173440 ⟨⟨184033636135, 184033636144⟩, ⟨179575099723, 188543760969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250347520 251658240 660602880 666173440 ⟨⟨182480952932, 182480952941⟩, ⟨178042640828, 186970690464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249036800 250347520 666173440 671744000 ⟨⟨185485707156, 185485707164⟩, ⟨181013389197, 190009635341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250347520 251658240 666173440 671744000 ⟨⟨183922284051, 183922284059⟩, ⟨179470217859, 188425800401⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247726080 671744000 677314560 ⟨⟨190095174856, 190095174864⟩, ⟨185568264752, 194674029214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 249036800 671744000 677314560 ⟨⟨188514325729, 188514325738⟩, ⟨184007863948, 193072575350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247726080 677314560 682885120 ⟨⟨191566751817, 191566751825⟩, ⟨187026011879, 196159449788⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247726080 249036800 677314560 682885120 ⟨⟨189975234660, 189975234668⟩, ⟨185454967586, 194547306417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 671744000 677314560 ⟨⟨186936848973, 186936848981⟩, ⟨182450750455, 191474578552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251658240 671744000 677314560 ⟨⟨185362707165, 185362707174⟩, ⟨180896887463, 189880000802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249036800 250347520 677314560 682885120 ⟨⟨188387074848, 188387074856⟩, ⟨183887196639, 192938603973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 677314560 682885120 ⟨⟨186802235205, 186802235213⟩, ⟨182322662458, 191333304703⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 660602880 682885120 t = true :=
  ⟨_, (join_sr (m := 671744000) (by decide) (join_su (m := 249036800) (by decide) (join_sr (m := 666173440) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 247726080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 666173440) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250347520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249036800) (by decide) (join_sr (m := 677314560) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 247726080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 677314560) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250347520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (63/80 : ℝ) (521/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  have e3 : (((682885120 : ℤ) : ℝ) / (D : ℝ)) = (521/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
