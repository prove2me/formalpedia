-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_75497472_r305397760_353894400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:56:29.557633+00:00
-- url     : https://prove2.me/submissions/55a74c29-cbe0-43b0-88f4-854d2adb8bde

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 9/100]`, `ρ ∈ [233/640, 27/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 69206016 305397760 317521920 ⟨⟨272993789751, 272993789765⟩, ⟨256645605185, 289884626774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 69206016 71303168 305397760 317521920 ⟨⟨269172264996, 269172265009⟩, ⟨253082156875, 285794523314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 69206016 317521920 329646080 ⟨⟨280504664763, 280504664777⟩, ⟨264182201613, 297350887368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69206016 71303168 317521920 329646080 ⟨⟨276645391719, 276645391730⟩, ⟨260575216305, 293229708729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 71303168 73400320 305397760 317521920 ⟨⟨265434787807, 265434787821⟩, ⟨249595338212, 281796158751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 73400320 75497472 305397760 317521920 ⟨⟨261777989652, 261777989666⟩, ⟨246182110308, 277885827792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 71303168 73400320 317521920 329646080 ⟨⟨272868861700, 272868861710⟩, ⟨257043905730, 289198571220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 73400320 75497472 317521920 329646080 ⟨⟨269171812055, 269171812066⟩, ⟨253585315188, 285253899560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 67108864 69206016 329646080 341770240 ⟨⟨287894716429, 287894716440⟩, ⟨271599305940, 304695660838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 69206016 71303168 329646080 341770240 ⟨⟨284000300879, 284000300891⟩, ⟨267951509473, 300545838668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 67108864 69206016 341770240 353894400 ⟨⟨295170219962, 295170219976⟩, ⟨278902981917, 311925399222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 69206016 71303168 341770240 353894400 ⟨⟨291243046400, 291243046414⟩, ⟨275216880459, 307749146113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 71303168 73400320 329646080 341770240 ⟨⟨280187306880, 280187306893⟩, ⟨264378399197, 296484363762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 73400320 75497472 329646080 341770240 ⟨⟨276452573876, 276452573890⟩, ⟨260877102404, 292507785133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 71303168 73400320 341770240 353894400 ⟨⟨287395962382, 287395962396⟩, ⟨271604450175, 303659555536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 73400320 75497472 341770240 353894400 ⟨⟨283625905652, 283625905666⟩, ⟨268062898036, 299653295248⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 75497472 305397760 353894400 t = true :=
  ⟨_, (join_sr (m := 329646080) (by decide) (join_su (m := 71303168) (by decide) (join_sr (m := 317521920) (by decide) (join_su (m := 69206016) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 69206016) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 317521920) (by decide) (join_su (m := 73400320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 73400320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 71303168) (by decide) (join_sr (m := 341770240) (by decide) (join_su (m := 69206016) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 69206016) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 341770240) (by decide) (join_su (m := 73400320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 73400320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  have e3 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
