-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_144179200_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:19:50.729154+00:00
-- url     : https://prove2.me/submissions/42871d58-ade9-4a30-bbcf-f62d2e9e5ffd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 11/64]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142213120 119275520 122224640 ⟨⟨74035853626, 74035853635⟩, ⟨71449404688, 76649724766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 142213120 142868480 119275520 122224640 ⟨⟨73704886338, 73704886341⟩, ⟨71128308137, 76308704560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 141557760 142213120 122224640 125173760 ⟨⟨75717149032, 75717149039⟩, ⟨73124274304, 78337390188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142213120 142868480 122224640 125173760 ⟨⟨75379627104, 75379627105⟩, ⟨72796638544, 77989801169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 142868480 143523840 119275520 122224640 ⟨⟨73375822611, 73375822619⟩, ⟨70809039790, 75969665201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 143523840 144179200 119275520 122224640 ⟨⟨73048642176, 73048642183⟩, ⟨70491580266, 75632585482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 142868480 143523840 122224640 125173760 ⟨⟨75044035637, 75044035643⟩, ⟨72470857989, 77644219775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 143523840 144179200 122224640 125173760 ⟨⟨74710354160, 74710354166⟩, ⟨72146913050, 77300624604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 142213120 125173760 128122880 ⟨⟨77393189516, 77393189523⟩, ⟨74793939088, 80019750397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 142213120 142868480 125173760 128122880 ⟨⟨77049172206, 77049172210⟩, ⟨74459822667, 79665652539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 141557760 142213120 128122880 131072000 ⟨⟨79064023457, 79064023465⟩, ⟨76458446756, 81696854442⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 142213120 142868480 128122880 131072000 ⟨⟨78713569243, 78713569247⟩, ⟨76117907449, 81336306917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 142868480 143523840 125173760 128122880 ⟨⟨76707111575, 76707111583⟩, ⟨74127587774, 79313588387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 143523840 144179200 125173760 128122880 ⟨⟨76366986961, 76366986968⟩, ⟨73797214632, 78963536359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 142868480 143523840 128122880 131072000 ⟨⟨78365097253, 78365097261⟩, ⟨75779275337, 80977818502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 143523840 144179200 128122880 131072000 ⟨⟨78018586645, 78018586652⟩, ⟨75442530455, 80621367440⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 144179200 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 142868480) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 142213120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 142213120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 143523840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 143523840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 142868480) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 142213120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 142213120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 143523840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 143523840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (11/64 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
