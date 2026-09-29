-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u120586240_123207680_r101580800_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:18:59.119885+00:00
-- url     : https://prove2.me/submissions/f4a38ddf-6df9-40e7-8daf-ac4a62c7e8ab

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/160, 47/320]`, `ρ ∈ [31/256, 41/320]` by 9 cells of the computing
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
theorem cell0 : cellOK 120586240 121241600 101580800 104529920 ⟨⟨74167562612, 74167562620⟩, ⟨71261953670, 77108298821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 121241600 121896960 101580800 104529920 ⟨⟨73810022443, 73810022453⟩, ⟨70917193250, 76737703130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 120586240 121241600 104529920 107479040 ⟨⟨76121321711, 76121321718⟩, ⟨73208378534, 79069280916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 121241600 121896960 104529920 107479040 ⟨⟨75755700229, 75755700238⟩, ⟨72855552963, 78690590130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 121896960 122552320 101580800 104529920 ⟨⟨73454995752, 73454995760⟩, ⟨70574831031, 76369739615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 122552320 123207680 101580800 103055360 ⟨⟨72618811297, 72618811301⟩, ⟨70362695260, 74896069760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 122552320 123207680 103055360 104529920 ⟨⟨73585597806, 73585597810⟩, ⟨71326285450, 75866028110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 121896960 122552320 104529920 107479040 ⟨⟨75392633235, 75392633242⟩, ⟨72505166831, 78314572252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 122552320 123207680 104529920 107479040 ⟨⟨75032089190, 75032089193⟩, ⟨72157190199, 77941194089⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 120586240 123207680 101580800 107479040 t = true :=
  ⟨_, (join_su (m := 121896960) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 121241600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 121241600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 104529920) (by decide) (join_su (m := 122552320) (by decide) (leaf_ok cell4) (join_sr (m := 103055360) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 122552320) (by decide) (leaf_ok cell7) (leaf_ok cell8))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (47/320 : ℝ) →
    rho ∈ Set.Icc (31/256 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e1 : (((123207680 : ℤ) : ℝ) / (D : ℝ)) = (47/320 : ℝ) := by norm_num [D]
  have e2 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
