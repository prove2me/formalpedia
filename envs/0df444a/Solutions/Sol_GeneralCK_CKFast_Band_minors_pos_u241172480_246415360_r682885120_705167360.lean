-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r682885120_705167360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:01:35.66146+00:00
-- url     : https://prove2.me/submissions/e02bff41-21a5-4e65-8c6e-31a3846fe1ee

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [521/640, 269/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 682885120 688455680 ⟨⟨199480210545, 199480210554⟩, ⟨194842813313, 204170174608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242483200 243793920 682885120 688455680 ⟨⟨197864302496, 197864302505⟩, ⟨193247739867, 202533283735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 242483200 688455680 694026240 ⟨⟨200992254641, 200992254650⟩, ⟨196340946742, 205696128164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 688455680 694026240 ⟨⟨199365785642, 199365785651⟩, ⟨194735331617, 204048660387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 245104640 682885120 688455680 ⟨⟨196251887524, 196251887533⟩, ⟨191656074203, 200899970699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245104640 246415360 682885120 688455680 ⟨⟨194642927354, 194642927357⟩, ⟨190067778639, 199270196637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243793920 245104640 688455680 694026240 ⟨⟨197742793049, 197742793058⟩, ⟨193133108740, 202404752582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245104640 246415360 688455680 694026240 ⟨⟨196123238850, 196123238854⟩, ⟨191534240679, 200764366172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 242483200 694026240 699596800 ⟨⟨202503296704, 202503296713⟩, ⟨197838081124, 207221075600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243793920 694026240 699596800 ⟨⟨200866288432, 200866288441⟩, ⟨196221945572, 205563053040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 242483200 699596800 705167360 ⟨⟨204013351859, 204013351867⟩, ⟨199334231437, 208745032182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242483200 243793920 699596800 705167360 ⟨⟨202365825631, 202365825640⟩, ⟨197707596356, 207076476597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 694026240 699596800 ⟨⟨199232739593, 199232739602⟩, ⟨194609186439, 203908572282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 246415360 694026240 699596800 ⟨⟨197602612443, 197602612447⟩, ⟨192999766540, 202257595033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243793920 245104640 699596800 705167360 ⟨⟨200721741571, 200721741580⟩, ⟨196084321574, 205411444344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 699596800 705167360 ⟨⟨199081062197, 199081062201⟩, ⟨194464370158, 203749897412⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 682885120 705167360 t = true :=
  ⟨_, (join_sr (m := 694026240) (by decide) (join_su (m := 243793920) (by decide) (join_sr (m := 688455680) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242483200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 688455680) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245104640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243793920) (by decide) (join_sr (m := 699596800) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 242483200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 699596800) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245104640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (521/640 : ℝ) (269/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((682885120 : ℤ) : ℝ) / (D : ℝ)) = (521/640 : ℝ) := by norm_num [D]
  have e3 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
