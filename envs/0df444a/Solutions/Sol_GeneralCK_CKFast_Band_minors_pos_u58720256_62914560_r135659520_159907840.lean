-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_62914560_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:13:14.454771+00:00
-- url     : https://prove2.me/submissions/969e30d8-d895-4aed-8337-4c76056833e7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 3/40]`, `ρ ∈ [207/1280, 61/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 58720256 59768832 135659520 141721600 ⟨⟨160650493513, 160650493527⟩, ⟨151518219963, 170050353443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 59768832 60817408 135659520 141721600 ⟨⟨159014562330, 159014562345⟩, ⟨149991274521, 168300182352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 58720256 59768832 141721600 147783680 ⟨⟨166099533462, 166099533474⟩, ⟨156966567921, 175494283694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 59768832 60817408 141721600 147783680 ⟨⟨164431749208, 164431749222⟩, ⟨155406490469, 173713758451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 60817408 61865984 135659520 141721600 ⟨⟨157409160948, 157409160960⟩, ⟨148492278636, 166583279353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 61865984 62914560 135659520 141721600 ⟨⟨155833349304, 155833349316⟩, ⟨147020383614, 164898606665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 60817408 61865984 141721600 147783680 ⟨⟨162794551840, 162794551854⟩, ⟨153874488105, 171966480067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 61865984 62914560 141721600 147783680 ⟨⟨161187013193, 161187013205⟩, ⟨152369720301, 170251426919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 58720256 59768832 147783680 153845760 ⟨⟨171460447524, 171460447539⟩, ⟨162328279768, 180848747058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 59768832 60817408 147783680 153845760 ⟨⟨169762508076, 169762508088⟩, ⟨160736756955, 179039567631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 58720256 59768832 153845760 159907840 ⟨⟨176736647917, 176736647929⟩, ⟨167606644425, 186117274882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 59768832 60817408 153845760 159907840 ⟨⟨175010146323, 175010146335⟩, ⟨165985261813, 184281033078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 60817408 61865984 147783680 153845760 ⟨⟨168095177614, 168095177628⟩, ⟨159173398520, 177263580695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 61865984 62914560 147783680 153845760 ⟨⟨166457540514, 166457540528⟩, ⟨157637372878, 175519781241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 60817408 61865984 153845760 159907840 ⟨⟨173314244425, 173314244437⟩, ⟨164392100129, 182477899896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 61865984 62914560 153845760 159907840 ⟨⟨171648039639, 171648039650⟩, ⟨162826337387, 180706887264⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 62914560 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 60817408) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 59768832) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 59768832) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 61865984) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 61865984) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 60817408) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 59768832) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 59768832) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 153845760) (by decide) (join_su (m := 61865984) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 61865984) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (3/40 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
