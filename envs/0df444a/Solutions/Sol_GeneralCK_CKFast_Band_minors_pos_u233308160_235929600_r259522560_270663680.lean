-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_235929600_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:06:01.408911+00:00
-- url     : https://prove2.me/submissions/eff7dbdb-ead9-44ac-92f9-3c200349d90b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 9/32]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 233308160 233963520 259522560 262307840 ⟨⟨84499035425, 84499035432⟩, ⟨82657566337, 86353502505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233963520 234618880 259522560 262307840 ⟨⟨84130633361, 84130633363⟩, ⟨82293846697, 85980371298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233963520 262307840 265093120 ⟨⟨85361649771, 85361649778⟩, ⟨83516418731, 87219886161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233963520 234618880 262307840 265093120 ⟨⟨84989808102, 84989808105⟩, ⟨83149268050, 86843306926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 234618880 235274240 259522560 262307840 ⟨⟨83763121549, 83763121556⟩, ⟨81930997604, 85608150322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235274240 235929600 259522560 262307840 ⟨⟨83396493819, 83396493825⟩, ⟨81569013012, 85236833261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 234618880 235274240 262307840 265093120 ⟨⟨84618861107, 84618861114⟩, ⟨82782992352, 86467642326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235274240 235929600 262307840 265093120 ⟨⟨84248802594, 84248802600⟩, ⟨82417585574, 86092886023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233963520 265093120 267878400 ⟨⟨86223556102, 86223556109⟩, ⟨84374565886, 88085558964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233963520 234618880 265093120 267878400 ⟨⟨85848283316, 85848283319⟩, ⟨84003992579, 87705540261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233963520 267878400 270663680 ⟨⟨87084757942, 87084757949⟩, ⟨85232011307, 88950524455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233963520 234618880 267878400 270663680 ⟨⟨86706062473, 86706062476⟩, ⟨84858023740, 88567074790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 234618880 235274240 265093120 267878400 ⟨⟨85473909544, 85473909550⟩, ⟨83634298614, 87326440514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235274240 235929600 265093120 267878400 ⟨⟨85100428576, 85100428582⟩, ⟨83265477907, 86948253368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235274240 267878400 270663680 ⟨⟨86328270278, 86328270285⟩, ⟨84484919791, 88184548322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235274240 235929600 267878400 270663680 ⟨⟨85951375131, 85951375139⟩, ⟨84112693365, 87802938681⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 235929600 259522560 270663680 t = true :=
  ⟨_, (join_sr (m := 265093120) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 262307840) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233963520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 262307840) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235274240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 234618880) (by decide) (join_sr (m := 267878400) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 233963520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 267878400) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235274240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
