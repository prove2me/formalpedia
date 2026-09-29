-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_170393600_r136970240_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:15:14.421042+00:00
-- url     : https://prove2.me/submissions/d29fa5f9-ec9c-4b8a-a684-cb524f142027

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 13/64]`, `ρ ∈ [209/1280, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 168427520 136970240 139755520 ⟨⟨70645273632, 70645273638⟩, ⟨68416813881, 72894105094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 168427520 169082880 136970240 139755520 ⟨⟨70344046231, 70344046234⟩, ⟨68122884081, 72585467137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 168427520 139755520 142540800 ⟨⟨71985231281, 71985231289⟩, ⟨69751544776, 74239271926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 168427520 169082880 139755520 142540800 ⟨⟨71678903358, 71678903363⟩, ⟨69452527996, 73925520465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 169082880 169738240 136970240 139755520 ⟨⟨70044206069, 70044206077⟩, ⟨67830294658, 72278264290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 169738240 170393600 136970240 139755520 ⟨⟨69745740407, 69745740415⟩, ⟨67539033340, 71972483323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 169082880 169738240 139755520 142540800 ⟨⟨71373979399, 71373979407⟩, ⟨69154868340, 73613220805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 169738240 170393600 139755520 142540800 ⟨⟨71070446552, 71070446560⟩, ⟨68858553427, 73302359605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 168427520 142540800 145326080 ⟨⟨73322341023, 73322341029⟩, ⟨71083450470, 75581567981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 168427520 169082880 142540800 145326080 ⟨⟨73010944209, 73010944213⟩, ⟨70779378004, 75262734983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 168427520 145326080 148111360 ⟨⟨74656623151, 74656623159⟩, ⟨72412551045, 76921013766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 168427520 169082880 145326080 148111360 ⟨⟨74340188765, 74340188768⟩, ⟨72103453880, 76597130880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 169082880 169738240 142540800 145326080 ⟨⟨72700967748, 72700967755⟩, ⟨70476679081, 74945370136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 169738240 170393600 142540800 145326080 ⟨⟨72392398681, 72392398689⟩, ⟨70175341209, 74629459995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 169082880 169738240 145326080 148111360 ⟨⟨74025190789, 74025190795⟩, ⟨71795746348, 76274732161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 169738240 170393600 145326080 148111360 ⟨⟨73711616162, 73711616170⟩, ⟨71489415855, 75953804066⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 170393600 136970240 148111360 t = true :=
  ⟨_, (join_sr (m := 142540800) (by decide) (join_su (m := 169082880) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 168427520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 168427520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 139755520) (by decide) (join_su (m := 169738240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 169738240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 169082880) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 168427520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 168427520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 145326080) (by decide) (join_su (m := 169738240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 169738240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (13/64 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
