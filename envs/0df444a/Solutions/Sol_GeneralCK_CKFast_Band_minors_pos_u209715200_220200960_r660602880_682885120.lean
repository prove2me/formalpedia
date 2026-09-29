-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r660602880_682885120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:01:58.522548+00:00
-- url     : https://prove2.me/submissions/124d2e78-4f06-46db-a027-8540ad5d49c8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [63/80, 521/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 660602880 666173440 ⟨⟨231524098525, 231524098534⟩, ⟨222752852487, 240459895864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 212336640 666173440 671744000 ⟨⟨233285467312, 233285467321⟩, ⟨224487474128, 242247846375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 214958080 660602880 666173440 ⟨⟨228190027333, 228190027342⟩, ⟨219485965612, 237058102907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 666173440 671744000 ⟨⟨229930966571, 229930966580⟩, ⟨221200131769, 238825675936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 212336640 671744000 677314560 ⟨⟨235045131423, 235045131433⟩, ⟨226220412829, 244034065549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 212336640 677314560 682885120 ⟨⟨236803116991, 236803117000⟩, ⟨227951694247, 245818579974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 214958080 671744000 677314560 ⟨⟨231670263217, 231670263227⟩, ⟨222912675137, 240591581735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212336640 214958080 677314560 682885120 ⟨⟨233407942318, 233407942328⟩, ⟨224623620316, 242355845784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 660602880 666173440 ⟨⟨224874164811, 224874164816⟩, ⟨216236667859, 233675129308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 217579520 666173440 671744000 ⟨⟨226594584447, 226594584451⟩, ⟨217930298588, 235422223983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 660602880 666173440 ⟨⟨221576118103, 221576118112⟩, ⟨213004577194, 230310571875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 220200960 666173440 671744000 ⟨⟨223275931070, 223275931079⟩, ⟨214677595266, 232037090601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214958080 217579520 671744000 677314560 ⟨⟨228313422161, 228313422165⟩, ⟨219622365293, 237167714103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214958080 217579520 677314560 682885120 ⟨⟨230030701946, 230030701951⟩, ⟨221312891540, 238911624071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 220200960 671744000 677314560 ⟨⟨224974221372, 224974221382⟩, ⟨216349106691, 233762066012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217579520 220200960 677314560 682885120 ⟨⟨226671011986, 226671011996⟩, ⟨218019134045, 235485521467⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 660602880 682885120 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 671744000) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 666173440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 666173440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212336640) (by decide) (join_sr (m := 677314560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 677314560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 671744000) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 666173440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 666173440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 217579520) (by decide) (join_sr (m := 677314560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 677314560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (63/80 : ℝ) (521/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((660602880 : ℤ) : ℝ) / (D : ℝ)) = (63/80 : ℝ) := by norm_num [D]
  have e3 : (((682885120 : ℤ) : ℝ) / (D : ℝ)) = (521/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
