-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:40:47.147493+00:00
-- url     : https://prove2.me/submissions/4581ab1e-f569-4177-9156-36b4d00be179

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 259522560 262307840 ⟨⟨95004224847, 95004224854⟩, ⟨91664653994, 98383918621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 214958080 216268800 262307840 265093120 ⟨⟨95963230657, 95963230664⟩, ⟨92616291306, 99350317595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 216268800 217579520 259522560 262307840 ⟨⟨94214307629, 94214307636⟩, ⟨90889853188, 97578626839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 262307840 265093120 ⟨⟨95166181814, 95166181821⟩, ⟨91834385701, 98537868369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 216268800 265093120 267878400 ⟨⟨96921261191, 96921261198⟩, ⟨93566960575, 100315733796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214958080 216268800 267878400 270663680 ⟨⟨97878321705, 97878321711⟩, ⟨94516667015, 101280172521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 217579520 265093120 267878400 ⟨⟨96117102523, 96117102530⟩, ⟨92777971666, 99496149235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216268800 217579520 267878400 270663680 ⟨⟨97067074863, 97067074869⟩, ⟨93720616147, 100453474589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218890240 259522560 262307840 ⟨⟨93428681061, 93428681067⟩, ⟨90119199512, 96777772346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217579520 218890240 262307840 265093120 ⟨⟨94373443212, 94373443218⟩, ⟨91056647013, 97729875801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 220200960 259522560 262307840 ⟨⟨92647284590, 92647284592⟩, ⟨89352634481, 95981292468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218890240 220200960 262307840 265093120 ⟨⟨93584954155, 93584954158⟩, ⟨90283016604, 96926277084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 265093120 267878400 ⟨⟨95317273292, 95317273299⟩, ⟨91993169069, 98681040303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 217579520 218890240 267878400 270663680 ⟨⟨96260176264, 96260176270⟩, ⟨92928770605, 99631270857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 220200960 265093120 267878400 ⟨⟨94521712669, 94521712673⟩, ⟨91212494006, 97870344067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218890240 220200960 267878400 270663680 ⟨⟨95457564952, 95457564955⟩, ⟨92141071474, 98813498277⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 259522560 270663680 t = true :=
  ⟨_, (join_su (m := 217579520) (by decide) (join_sr (m := 265093120) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 262307840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 216268800) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 267878400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 265093120) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 262307840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 218890240) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 267878400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
