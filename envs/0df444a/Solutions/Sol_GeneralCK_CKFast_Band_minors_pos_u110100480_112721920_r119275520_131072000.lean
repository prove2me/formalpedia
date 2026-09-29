-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_112721920_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:11:38.466724+00:00
-- url     : https://prove2.me/submissions/3ad99abf-e9bd-4cfe-9f7e-8be93844b51b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 43/320]`, `ρ ∈ [91/640, 5/32]` by 14 cells of the computing
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
theorem cell0 : cellOK 110100480 110755840 119275520 122224640 ⟨⟨92646491125, 92646491135⟩, ⟨89475586573, 95856513353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 110755840 111411200 119275520 122224640 ⟨⟨92193029882, 92193029890⟩, ⟨89037037758, 95387819912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 110755840 122224640 125173760 ⟨⟨94678315762, 94678315770⟩, ⟨91500489565, 97895103533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110755840 111411200 122224640 125173760 ⟨⟨94216745543, 94216745552⟩, ⟨91053833697, 97418302426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 111411200 112066560 119275520 122224640 ⟨⟨91742921205, 91742921212⟩, ⟨88601698723, 94922625950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 112066560 112721920 119275520 122224640 ⟨⟨91296121805, 91296121813⟩, ⟨88169528279, 94460886004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 111411200 112066560 122224640 125173760 ⟨⟨93758566061, 93758566068⟩, ⟨90610426339, 96945038337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 112066560 112721920 122224640 125173760 ⟨⟨93303733760, 93303733768⟩, ⟨90170226015, 96475265564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 110755840 125173760 128122880 ⟨⟨96701019107, 96701019117⟩, ⟨93516369476, 99924474404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 110755840 111411200 125173760 128122880 ⟨⟨96231446045, 96231446053⟩, ⟨93061711345, 99439673079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 110100480 111411200 128122880 131072000 ⟨⟨98475538348, 98475538356⟩, ⟨93502894554, 103542737055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 111411200 112066560 125173760 128122880 ⟨⟨95765300540, 95765300550⟩, ⟨92610339122, 98958444956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 112066560 112721920 125173760 128122880 ⟨⟨95302538799, 95302538809⟩, ⟨92162211069, 98480744110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 111411200 112721920 128122880 131072000 ⟨⟨97527510170, 97527510178⟩, ⟨92597758567, 102550403499⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 112721920 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 111411200) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 110755840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 110755840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 112066560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 112066560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 111411200) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 110755840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 128122880) (by decide) (join_su (m := 112066560) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (43/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
