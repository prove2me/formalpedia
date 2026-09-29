-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_136314880_r414187520_461373440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:51:41.531627+00:00
-- url     : https://prove2.me/submissions/964f676d-f203-42ac-b82e-f850d96592b2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 13/80]`, `ρ ∈ [79/160, 11/20]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 128450560 414187520 425984000 ⟨⟨242758804170, 242758804181⟩, ⟨229749958378, 256134699578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 128450560 131072000 414187520 425984000 ⟨⟨239363311895, 239363311907⟩, ⟨226518910920, 252569820967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 128450560 425984000 437780480 ⟨⟨248323388712, 248323388723⟩, ⟨235263931320, 261744427802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 128450560 131072000 425984000 437780480 ⟨⟨244880036814, 244880036825⟩, ⟨231983575108, 258133426850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131072000 133693440 414187520 425984000 ⟨⟨236016470038, 236016470048⟩, ⟨223333114548, 249057073528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 133693440 136314880 414187520 425984000 ⟨⟨232716786795, 232716786805⟩, ⟨220191187066, 245594855004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131072000 133693440 425984000 437780480 ⟨⟨241484963766, 241484963776⟩, ⟨228748201305, 254574070565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 133693440 136314880 425984000 437780480 ⟨⟨238136706233, 238136706244⟩, ⟨225556450957, 251064790907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 128450560 437780480 449576960 ⟨⟨253846967277, 253846967287⟩, ⟨240737923976, 267312150072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 128450560 131072000 437780480 449576960 ⟨⟨250356961138, 250356961149⟩, ⟨237409446379, 263656244022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 128450560 449576960 461373440 ⟨⟨259330955794, 259330955805⟩, ⟨246173300150, 272839333832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 128450560 131072000 449576960 461373440 ⟨⟨255795443055, 255795443064⟩, ⟨242797833013, 269139680128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 131072000 133693440 437780480 449576960 ⟨⟨246914838978, 246914838989⟩, ⟨234125657732, 260051474871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 133693440 136314880 437780480 449576960 ⟨⟨243519165805, 243519165816⟩, ⟨230885222386, 256496308437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 131072000 133693440 449576960 461373440 ⟨⟨252307398192, 252307398201⟩, ⟨239466738606, 265490636387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133693440 136314880 449576960 461373440 ⟨⟨248865414368, 248865414379⟩, ⟨236178704594, 261890701866⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 136314880 414187520 461373440 t = true :=
  ⟨_, (join_sr (m := 437780480) (by decide) (join_su (m := 131072000) (by decide) (join_sr (m := 425984000) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 128450560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 425984000) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 133693440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 131072000) (by decide) (join_sr (m := 449576960) (by decide) (join_su (m := 128450560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 128450560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 449576960) (by decide) (join_su (m := 133693440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 133693440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (79/160 : ℝ) (11/20 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  have e3 : (((461373440 : ℤ) : ℝ) / (D : ℝ)) = (11/20 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
