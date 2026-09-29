-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r772014080_794296320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:11:12.97221+00:00
-- url     : https://prove2.me/submissions/c099cd5b-d725-4d6c-9bd6-b26f23e9f386

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [589/640, 303/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 772014080 777584640 ⟨⟨223561034443, 223561034452⟩, ⟨218701343390, 228473138125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242483200 243793920 772014080 777584640 ⟨⟨221778555512, 221778555521⟩, ⟨216939958991, 226669471677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 242483200 777584640 783155200 ⟨⟨225058828368, 225058828378⟩, ⟨220185256981, 229984792942⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 777584640 783155200 ⟨⟨223266093476, 223266093486⟩, ⟨218413629652, 228170861109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 245104640 772014080 777584640 ⟨⟨219999270078, 219999270087⟩, ⟨215181701601, 224869063813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245104640 246415360 772014080 777584640 ⟨⟨218223144234, 218223144239⟩, ⟨213426537646, 223071880312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243793920 245104640 777584640 783155200 ⟨⟨221476531293, 221476531304⟩, ⟨216645109755, 226360165807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245104640 246415360 777584640 783155200 ⟨⟨219690108193, 219690108197⟩, ⟨214879663983, 224552673106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 242483200 783155200 788725760 ⟨⟨226555855425, 226555855434⟩, ⟨221668404368, 231495679038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243793920 783155200 788725760 ⟨⟨224752880766, 224752880775⟩, ⟨219886549949, 229671498382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 242483200 788725760 794296320 ⟨⟨228052129868, 228052129877⟩, ⟨223150799660, 233005810806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242483200 243793920 788725760 794296320 ⟨⟨226238931304, 226238931313⟩, ⟨221358733670, 231171397557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 783155200 788725760 ⟨⟨222953057815, 222953057824⟩, ⟨218107783180, 227850531988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 246415360 783155200 788725760 ⟨⟨221156353227, 221156353231⟩, ⟨216332071020, 226032746221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243793920 245104640 788725760 794296320 ⟨⟨224428863246, 224428863255⟩, ⟨219569735346, 229340176091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 788725760 794296320 ⟨⟨222621892629, 222621892633⟩, ⟨217783771914, 227512113072⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 772014080 794296320 t = true :=
  ⟨_, (join_sr (m := 783155200) (by decide) (join_su (m := 243793920) (by decide) (join_sr (m := 777584640) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242483200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 777584640) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245104640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243793920) (by decide) (join_sr (m := 788725760) (by decide) (join_su (m := 242483200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 242483200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 788725760) (by decide) (join_su (m := 245104640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245104640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (589/640 : ℝ) (303/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((772014080 : ℤ) : ℝ) / (D : ℝ)) = (589/640 : ℝ) := by norm_num [D]
  have e3 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
