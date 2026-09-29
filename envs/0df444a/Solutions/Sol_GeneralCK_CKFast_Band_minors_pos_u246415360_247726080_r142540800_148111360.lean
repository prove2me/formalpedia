-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_247726080_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:52:31.14702+00:00
-- url     : https://prove2.me/submissions/bf8a5179-c8ee-429b-b21c-e41a51ba970d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 189/640]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 246743040 142540800 143933440 ⟨⟨43228974675, 43228974678⟩, ⟨42427871382, 44032994125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246743040 247070720 142540800 143933440 ⟨⟨43127330389, 43127330394⟩, ⟨42327203406, 43930367808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 246743040 143933440 145326080 ⟨⟨43639773135, 43639773138⟩, ⟨42837753224, 44444710677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 246743040 247070720 143933440 145326080 ⟨⟨43537204914, 43537204919⟩, ⟨42736162747, 44341158999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247070720 247398400 142540800 143933440 ⟨⟨43025820185, 43025820190⟩, ⟨42226667392, 43827877715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247398400 247726080 142540800 143933440 ⟨⟨42924443562, 42924443567⟩, ⟨42126262837, 43725523338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247398400 143933440 145326080 ⟨⟨43434771720, 43434771725⟩, ⟨42634705171, 44237744489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247398400 247726080 143933440 145326080 ⟨⟨43332473047, 43332473052⟩, ⟨42533379995, 44134466637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 246743040 145326080 146718720 ⟨⟨44050402721, 44050402722⟩, ⟨43247466434, 44856258109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 246743040 247070720 145326080 146718720 ⟨⟨43946911685, 43946911690⟩, ⟨43144954570, 44751782192⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 246743040 146718720 148111360 ⟨⟨44460863812, 44460863815⟩, ⟨43657011395, 45267636801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 246743040 247070720 146718720 148111360 ⟨⟨44356451079, 44356451084⟩, ⟨43553579256, 45162237768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247070720 247398400 145326080 146718720 ⟨⟨43843556614, 43843556619⟩, ⟨43042576544, 44647444384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247398400 247726080 145326080 146718720 ⟨⟨43740336998, 43740337003⟩, ⟨42940331850, 44543244171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247070720 247398400 146718720 148111360 ⟨⟨44252175241, 44252175247⟩, ⟨43450281884, 45056977777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 247398400 247726080 146718720 148111360 ⟨⟨44148035788, 44148035793⟩, ⟨43347118773, 44951856311⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 247726080 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 246743040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 247398400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 247070720) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 246743040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 246743040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 247398400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 247398400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (189/640 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
