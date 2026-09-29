-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u226754560_228065280_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:59:04.237802+00:00
-- url     : https://prove2.me/submissions/79f1bf04-a9f5-4e51-8c53-1593f88ba193

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [173/640, 87/320]`, `ρ ∈ [87/512, 113/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 226754560 227082240 142540800 143933440 ⟨⟨49593277115, 49593277119⟩, ⟨48729390496, 50460459800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 227082240 227409920 142540800 143933440 ⟨⟨49482585819, 49482585824⟩, ⟨48619818677, 50348642048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226754560 227082240 143933440 145326080 ⟨⟨50061358792, 50061358796⟩, ⟨49196466542, 50929548202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 227082240 227409920 143933440 145326080 ⟨⟨49949681030, 49949681037⟩, ⟨49085909791, 50816742461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 227409920 227737600 142540800 143933440 ⟨⟨49372062887, 49372062894⟩, ⟨48510412562, 50236995348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 227737600 228065280 142540800 143933440 ⟨⟨49261707674, 49261707680⟩, ⟨48401171508, 50125519044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 227409920 227737600 143933440 145326080 ⟨⟨49838172778, 49838172783⟩, ⟨48975519884, 50704108916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227737600 228065280 143933440 145326080 ⟨⟨49726833383, 49726833389⟩, ⟨48865296179, 50591646910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 226754560 227409920 145326080 146718720 ⟨⟨50472839523, 50472839528⟩, ⟨49011555905, 51943230965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226754560 227409920 146718720 148111360 ⟨⟨50939933522, 50939933527⟩, ⟨49476809769, 52412170301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 227409920 228065280 145326080 146718720 ⟨⟨50247855274, 50247855276⟩, ⟨48789726294, 51715059395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 227409920 228065280 146718720 148111360 ⟨⟨50712984741, 50712984744⟩, ⟨49253020637, 52182029224⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 226754560 228065280 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 227409920) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 227082240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 227082240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 227737600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 227737600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 227409920) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 146718720) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (173/640 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((226754560 : ℤ) : ℝ) / (D : ℝ)) = (173/640 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
