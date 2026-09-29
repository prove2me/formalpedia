-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r305397760_353894400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:31:34.740556+00:00
-- url     : https://prove2.me/submissions/42182a05-0a70-4a5f-a667-88b9ce4f5e25

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 3/100]`, `ρ ∈ [233/640, 27/64]` by 12 cells of the computing
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
theorem cell0 : cellOK 16777216 18874368 305397760 317521920 ⟨⟨405036006123, 405036006144⟩, ⟨378667759054, 432271317424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 18874368 20971520 305397760 317521920 ⟨⟨397054472641, 397054472662⟩, ⟨371360396741, 423603960522⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 16777216 18874368 317521920 329646080 ⟨⟨412510063514, 412510063532⟩, ⟨386521526623, 439301977793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 18874368 20971520 317521920 329646080 ⟨⟨404602862393, 404602862410⟩, ⟨379258170671, 430742625468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 20971520 23068672 305397760 317521920 ⟨⟨389419483385, 389419483405⟩, ⟨364359724573, 415321362886⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 23068672 25165824 305397760 317521920 ⟨⟨382099754823, 382099754843⟩, ⟨357639274796, 407388041156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 20971520 23068672 317521920 329646080 ⟨⟨397030625655, 397030625671⟩, ⟨372292353110, 422553828858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 23068672 25165824 317521920 329646080 ⟨⟨389763309502, 389763309518⟩, ⟨365598582206, 414701620398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 16777216 20971520 329646080 341770240 ⟨⟨415866377629, 415866377649⟩, ⟨378343772732, 455022914664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 16777216 20971520 341770240 353894400 ⟨⟨423073096588, 423073096609⟩, ⟨385980410778, 461682943111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 20971520 25165824 329646080 341770240 ⟨⟨400837709217, 400837709237⟩, ⟨365061926372, 438238615362⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 20971520 25165824 341770240 353894400 ⟨⟨408165046744, 408165046760⟩, ⟨372750865408, 445098733107⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 25165824 305397760 353894400 t = true :=
  ⟨_, (join_sr (m := 329646080) (by decide) (join_su (m := 20971520) (by decide) (join_sr (m := 317521920) (by decide) (join_su (m := 18874368) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 18874368) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 317521920) (by decide) (join_su (m := 23068672) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 23068672) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 20971520) (by decide) (join_sr (m := 341770240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 341770240) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  have e3 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
