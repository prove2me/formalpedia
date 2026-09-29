-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u175636480_178257920_r148111360_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:50.539578+00:00
-- url     : https://prove2.me/submissions/da5363c3-7b40-4ee6-b3ea-4a935268c095

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [67/320, 17/80]`, `ρ ∈ [113/640, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 175636480 176291840 148111360 150896640 ⟨⟨72223826415, 72223826423⟩, ⟨70059806982, 74406879004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 176291840 176947200 148111360 150896640 ⟨⟨71918975172, 71918975180⟩, ⟨69761774094, 74095109553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 175636480 176291840 150896640 153681920 ⟨⟨73493799718, 73493799724⟩, ⟨71324792106, 75681828435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 176291840 176947200 150896640 153681920 ⟨⟨73184151400, 73184151406⟩, ⟨71021974748, 75365249768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 176947200 177602560 148111360 150896640 ⟨⟨71615427783, 71615427791⟩, ⟨69465003533, 73784686324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 177602560 178257920 148111360 150896640 ⟨⟨71313172788, 71313172795⟩, ⟨69169484238, 73475597444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 176947200 177602560 150896640 153681920 ⟨⟨72875821241, 72875821249⟩, ⟨70720434044, 75050031596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 177602560 178257920 150896640 153681920 ⟨⟨72568797695, 72568797701⟩, ⟨70420158844, 74736161965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 175636480 176291840 153681920 156467200 ⟨⟨74761349971, 74761349978⟩, ⟨72587372478, 76954336370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 176291840 176947200 153681920 156467200 ⟨⟨74446931411, 74446931417⟩, ⟨72279797208, 76632975594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 176291840 156467200 159252480 ⟨⟨76026493497, 76026493503⟩, ⟨73847564262, 78224419291⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 176291840 176947200 156467200 159252480 ⟨⟨75707331277, 75707331285⟩, ⟨73535257392, 77898303264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 176947200 177602560 153681920 156467200 ⟨⟨74133845039, 74133845047⟩, ⟨71973512646, 76312989310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 177602560 178257920 153681920 156467200 ⟨⟨73822079223, 73822079230⟩, ⟨71668507554, 75994365481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 176947200 177602560 156467200 159252480 ⟨⟨75389515005, 75389515013⟩, ⟨73224255015, 77573575449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 177602560 178257920 156467200 159252480 ⟨⟨75073032961, 75073032969⟩, ⟨72914545808, 77250223727⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 175636480 178257920 148111360 159252480 t = true :=
  ⟨_, (join_sr (m := 153681920) (by decide) (join_su (m := 176947200) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 176291840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 176291840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 150896640) (by decide) (join_su (m := 177602560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 177602560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 176947200) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 176291840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 176291840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 156467200) (by decide) (join_su (m := 177602560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 177602560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (67/320 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
