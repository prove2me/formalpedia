-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_107479040_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:10:55.962412+00:00
-- url     : https://prove2.me/submissions/cb7774b5-6e7f-433a-9352-b1a6e9617fb3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 41/320]`, `ρ ∈ [91/640, 5/32]` by 10 cells of the computing
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
theorem cell0 : cellOK 104857600 105512960 119275520 122224640 ⟨⟨96400330457, 96400330466⟩, ⟨93104720409, 99737773965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 105512960 106168320 119275520 122224640 ⟨⟨95918394126, 95918394134⟩, ⟨92638919483, 99239346673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 106168320 122224640 125173760 ⟨⟨98252778405, 98252778413⟩, ⟨93124175128, 103482709891⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 106168320 106823680 119275520 122224640 ⟨⟨95440185911, 95440185915⟩, ⟨92176685522, 98744813408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 106823680 107479040 119275520 122224640 ⟨⟨94965655843, 94965655853⟩, ⟨91717971026, 98254121655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 106168320 107479040 122224640 125173760 ⟨⟨97279582270, 97279582278⟩, ⟨92197386831, 102461506515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 104857600 106168320 125173760 128122880 ⟨⟨100336701487, 100336701495⟩, ⟨95195881461, 105578478106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 104857600 106168320 128122880 131072000 ⟨⟨102410786386, 102410786396⟩, ⟨97257911527, 107664246175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 106168320 107479040 125173760 128122880 ⟨⟨99346970401, 99346970409⟩, ⟨94252561227, 104540753107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 106168320 107479040 128122880 131072000 ⟨⟨101404748293, 101404748303⟩, ⟨96298282935, 106610231779⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 107479040 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 106168320) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 105512960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 122224640) (by decide) (join_su (m := 106823680) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 106168320) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 128122880) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (41/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
