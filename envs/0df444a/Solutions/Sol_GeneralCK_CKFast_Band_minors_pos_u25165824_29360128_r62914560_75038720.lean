-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:19:12.47959+00:00
-- url     : https://prove2.me/submissions/5f7aaaad-56c3-499b-8352-c577ce97f62e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 7/200]`, `ρ ∈ [3/40, 229/2560]` by 20 cells of the computing
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
theorem cell0 : cellOK 25165824 25690112 62914560 65945600 ⟨⟨142927385704, 142927385724⟩, ⟨134557501926, 151565258647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 25690112 26214400 62914560 65945600 ⟨⟨141404699692, 141404699711⟩, ⟨133147943451, 149923147691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 25165824 26214400 65945600 68976640 ⟨⟨147008619995, 147008620014⟩, ⟨135161068002, 159399503092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 26214400 26738688 62914560 65945600 ⟨⟨139916278851, 139916278875⟩, ⟨131769513425, 148318665913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 26738688 27262976 62914560 65945600 ⟨⟨138460906222, 138460906240⟩, ⟨130421123724, 146750456568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 26214400 27262976 65945600 68976640 ⟨⟨143980670435, 143980670453⟩, ⟨132437989357, 156042462838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 25165824 26214400 68976640 72007680 ⟨⟨151750077106, 151750077125⟩, ⟨139934409005, 164095461996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 25165824 26214400 72007680 75038720 ⟨⟨156390768438, 156390768457⟩, ⟨144608543732, 168689555249⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 26214400 27262976 68976640 72007680 ⟨⟨148675017284, 148675017303⟩, ⟨137159625523, 160696949256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 26214400 27262976 72007680 75038720 ⟨⟨153272019055, 153272019073⟩, ⟨141785502243, 165252912740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 27262976 27787264 62914560 65945600 ⟨⟨137037423577, 137037423600⟩, ⟨129101738012, 145217229240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 27787264 28311552 62914560 65945600 ⟨⟨135644727849, 135644727868⟩, ⟨127810368622, 143717755750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 27262976 28311552 65945600 68976640 ⟨⟨141082645378, 141082645396⟩, ⟨129828636986, 152833201501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 28311552 28835840 62914560 65945600 ⟨⟨134281767780, 134281767803⟩, ⟨126546073634, 142250866411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 28835840 29360128 62914560 65945600 ⟨⟨132947540879, 132947540897⟩, ⟨125307954202, 140815446458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 28311552 29360128 65945600 68976640 ⟨⟨138305839259, 138305839277⟩, ⟨127325564877, 149761604452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 27262976 28311552 68976640 72007680 ⟨⟨145729748027, 145729748045⟩, ⟨134498896665, 157445518752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 27262976 28311552 72007680 75038720 ⟨⟨150282791400, 150282791418⟩, ⟨139076696018, 161962540322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 28311552 29360128 68976640 72007680 ⟨⟨142905698191, 142905698214⟩, ⟨131944858812, 154331253969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 28311552 29360128 72007680 75038720 ⟨⟨147414652764, 147414652782⟩, ⟨136474850217, 158808720281⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 29360128 62914560 75038720 t = true :=
  ⟨_, (join_su (m := 27262976) (by decide) (join_sr (m := 68976640) (by decide) (join_su (m := 26214400) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 25690112) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 65945600) (by decide) (join_su (m := 26738688) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 26214400) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 72007680) (by decide) (leaf_ok cell8) (leaf_ok cell9)))) (join_sr (m := 68976640) (by decide) (join_su (m := 28311552) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 27787264) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12)) (join_sr (m := 65945600) (by decide) (join_su (m := 28835840) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (leaf_ok cell15))) (join_su (m := 28311552) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_sr (m := 72007680) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (7/200 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
