-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r499384320_547880960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:55:37.842992+00:00
-- url     : https://prove2.me/submissions/ef6aa8f3-752b-479a-bd40-f6e90ed1f53c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 3/50]`, `ρ ∈ [381/640, 209/320]` by 15 cells of the computing
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
theorem cell0 : cellOK 33554432 37748736 499384320 511508480 ⟨⟨457004938177, 457004938194⟩, ⟨427937799968, 486773778440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 33554432 37748736 511508480 523632640 ⟨⟨463174073456, 463174073472⟩, ⟨434251768132, 492756927669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 37748736 41943040 499384320 511508480 ⟨⟨445951830782, 445951830800⟩, ⟨417641247706, 474980183378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 37748736 41943040 511508480 523632640 ⟨⟨452146930786, 452146930804⟩, ⟨423959633055, 481013156351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 33554432 37748736 523632640 547880960 ⟨⟨472316373182, 472316373198⟩, ⟨434765514996, 510882172398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 37748736 41943040 523632640 535756800 ⟨⟨458281932552, 458281932568⟩, ⟨430214911553, 486990375527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 37748736 41943040 535756800 547880960 ⟨⟨464360016437, 464360016454⟩, ⟨436410330751, 492914870881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 41943040 46137344 499384320 511508480 ⟨⟨435360791553, 435360791567⟩, ⟨407760838497, 463689254567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 41943040 46137344 511508480 523632640 ⟨⟨441571801288, 441571801304⟩, ⟨414075482326, 469760000092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 46137344 50331648 499384320 511508480 ⟨⟨425187751639, 425187751654⟩, ⟨398258593087, 452852158176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 46137344 50331648 511508480 523632640 ⟨⟨431405721455, 431405721470⟩, ⟨404562234663, 458949937591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 41943040 46137344 523632640 535756800 ⟨⟨447722909184, 447722909199⟩, ⟨420327875588, 475774380626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 41943040 46137344 535756800 547880960 ⟨⟨453817219756, 453817219770⟩, ⟨426521157452, 481735394526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 46137344 50331648 523632640 535756800 ⟨⟨437564264555, 437564264570⟩, ⟨410804669098, 464991124773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 46137344 50331648 535756800 547880960 ⟨⟨443666398042, 443666398057⟩, ⟨416988921895, 470978667110⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 50331648 499384320 547880960 t = true :=
  ⟨_, (join_su (m := 41943040) (by decide) (join_sr (m := 523632640) (by decide) (join_su (m := 37748736) (by decide) (join_sr (m := 511508480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 511508480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 37748736) (by decide) (leaf_ok cell4) (join_sr (m := 535756800) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 523632640) (by decide) (join_su (m := 46137344) (by decide) (join_sr (m := 511508480) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 511508480) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 46137344) (by decide) (join_sr (m := 535756800) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 535756800) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (381/640 : ℝ) (209/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((499384320 : ℤ) : ℝ) / (D : ℝ)) = (381/640 : ℝ) := by norm_num [D]
  have e3 : (((547880960 : ℤ) : ℝ) / (D : ℝ)) = (209/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
