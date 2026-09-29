-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_175636480_r136970240_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:34.332603+00:00
-- url     : https://prove2.me/submissions/72cd95bd-1693-4421-8651-d8d405381bbf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 67/320]`, `ρ ∈ [209/1280, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 173670400 136970240 139755520 ⟨⟨68273593890, 68273593896⟩, ⟨66102228796, 70464454464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173670400 174325760 136970240 139755520 ⟨⟨67983115851, 67983115858⟩, ⟨65818686343, 70166935573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173015040 173670400 139755520 142540800 ⟨⟨69573209514, 69573209522⟩, ⟨67396726596, 71769174562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 173670400 174325760 139755520 142540800 ⟨⟨69277761701, 69277761709⟩, ⟨67108228065, 71466672690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 174325760 174981120 136970240 139755520 ⟨⟨67693927196, 67693927202⟩, ⟨65536390025, 69870750224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 174981120 175636480 136970240 139755520 ⟨⟨67406016328, 67406016331⟩, ⟨65255328668, 69575886387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 174325760 174981120 139755520 142540800 ⟨⟨68983619137, 68983619142⟩, ⟨66820991543, 71165520206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 174981120 175636480 139755520 142540800 ⟨⟨68690770117, 68690770120⟩, ⟨66535005756, 70865704970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 173670400 142540800 145326080 ⟨⟨70870221108, 70870221115⟩, ⟨68688640502, 73071270338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 173670400 174325760 142540800 145326080 ⟨⟨70569832577, 70569832583⟩, ⟨68395214642, 72763814847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 173015040 173670400 145326080 148111360 ⟨⟨72164646593, 72164646600⟩, ⟨69977988253, 74370759892⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 173670400 174325760 145326080 148111360 ⟨⟨71859346124, 71859346130⟩, ⟨69679663547, 74058379861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 174325760 174981120 142540800 145326080 ⟨⟨70270764850, 70270764858⟩, ⟨68103066369, 72457724276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 174981120 175636480 142540800 145326080 ⟨⟨69973006128, 69973006132⟩, ⟨67812184301, 72152986387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 174325760 174981120 145326080 148111360 ⟨⟨71555381714, 71555381721⟩, ⟨69382631702, 73747379978⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 174981120 175636480 145326080 148111360 ⟨⟨71252741468, 71252741471⟩, ⟨69086881241, 73437747911⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 175636480 136970240 148111360 t = true :=
  ⟨_, (join_sr (m := 142540800) (by decide) (join_su (m := 174325760) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 173670400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 173670400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 139755520) (by decide) (join_su (m := 174981120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 174981120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 174325760) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 173670400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 173670400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 145326080) (by decide) (join_su (m := 174981120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 174981120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (67/320 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
