-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_201850880_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:15:46.564524+00:00
-- url     : https://prove2.me/submissions/b671948a-fa3c-4b66-866b-5f4b70f9e30a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 77/320]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 199884800 170393600 173178880 ⟨⟨70796612139, 70796612145⟩, ⟨68818524204, 72790607852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199884800 200540160 170393600 173178880 ⟨⟨70498135914, 70498135920⟩, ⟨68525687870, 72486418989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 199884800 173178880 175964160 ⟨⟨71889664868, 71889664875⟩, ⟨69907128445, 73888108845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 199884800 200540160 173178880 175964160 ⟨⟨71586998584, 71586998590⟩, ⟨69610113434, 73579718808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 200540160 201195520 170393600 173178880 ⟨⟨70200706670, 70200706677⟩, ⟨68233868636, 72183307523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201195520 201850880 170393600 173178880 ⟨⟨69904316085, 69904316090⟩, ⟨67943058430, 71881264872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 200540160 201195520 173178880 175964160 ⟨⟨71285389256, 71285389263⟩, ⟨69314125505, 73272416131⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201195520 201850880 173178880 175964160 ⟨⟨70984828507, 70984828511⟩, ⟨69019156529, 72966192181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 199884800 175964160 178749440 ⟨⟨72981179309, 72981179315⟩, ⟨70994204082, 74984061757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 199884800 200540160 175964160 178749440 ⟨⟨72674340382, 72674340388⟩, ⟨70693027646, 74671488126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 199884800 178749440 181534720 ⟨⟨74071164404, 74071164411⟩, ⟨72079759990, 76078475596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 199884800 200540160 178749440 181534720 ⟨⟨73760170115, 73760170122⟩, ⟨71774439248, 75761735817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 200540160 201195520 175964160 178749440 ⟨⟨72368568214, 72368568220⟩, ⟨70392888102, 74360011647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 201195520 201850880 175964160 178749440 ⟨⟨72063854374, 72063854375⟩, ⟨70093777269, 74049623628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 200540160 201195520 178749440 181534720 ⟨⟨73450252219, 73450252225⟩, ⟨71470165042, 75446102808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 201195520 201850880 178749440 181534720 ⟨⟨73141402229, 73141402232⟩, ⟨71166929134, 75131567826⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 201850880 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 199884800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 201195520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 200540160) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 199884800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 201195520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (77/320 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
