-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_37748736_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:44:30.288008+00:00
-- url     : https://prove2.me/submissions/a608f65a-c1d2-4edf-8f93-0e69f03b33cb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 9/200]`, `ρ ∈ [207/1280, 61/320]` by 13 cells of the computing
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
theorem cell0 : cellOK 33554432 34603008 135659520 141721600 ⟨⟨212514819434, 212514819454⟩, ⟨199643652019, 225851931183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 34603008 35651584 135659520 141721600 ⟨⟨209702743364, 209702743384⟩, ⟨197048096189, 222811028493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 33554432 34603008 141721600 147783680 ⟨⟨218684660540, 218684660556⟩, ⟨205880336382, 231938546811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 34603008 35651584 141721600 147783680 ⟨⟨215847934817, 215847934837⟩, ⟨203254989900, 228878911913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 35651584 36700160 135659520 141721600 ⟨⟨206965338420, 206965338439⟩, ⟨194519968630, 219852532655⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 36700160 37748736 135659520 141721600 ⟨⟨204299359752, 204299359767⟩, ⟨192056386965, 216972810341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 35651584 36700160 141721600 147783680 ⟨⟨213084943376, 213084943395⟩, ⟨200696447188, 225900389473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 36700160 37748736 141721600 147783680 ⟨⟨210392536482, 210392536498⟩, ⟨198201899344, 222999466093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 33554432 35651584 147783680 153845760 ⟨⟨223275457359, 223275457378⟩, ⟨204963750150, 242520066837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 33554432 35651584 153845760 159907840 ⟨⟨229162287314, 229162287334⟩, ⟨210926343675, 248300995796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 35651584 36700160 147783680 153845760 ⟨⟨219069356714, 219069356733⟩, ⟨206738559721, 231812880756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 36700160 37748736 147783680 153845760 ⟨⟨216353061935, 216353061954⟩, ⟨204215694046, 228893143369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 35651584 37748736 153845760 159907840 ⟨⟨223548174372, 223548174388⟩, ⟨205867236088, 242090247187⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 37748736 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 35651584) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 34603008) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 34603008) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 36700160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 36700160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 35651584) (by decide) (join_sr (m := 153845760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 153845760) (by decide) (join_su (m := 36700160) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (9/200 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
