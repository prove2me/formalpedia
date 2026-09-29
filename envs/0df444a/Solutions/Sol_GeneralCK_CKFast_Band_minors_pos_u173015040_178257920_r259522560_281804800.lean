-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r259522560_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.17228+00:00
-- url     : https://prove2.me/submissions/5df538ab-d28a-4178-82d3-03116a51369e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [99/320, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 259522560 265093120 ⟨⟨123569359486, 123569359491⟩, ⟨118831661490, 128381947732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 174325760 175636480 259522560 265093120 ⟨⟨122599050761, 122599050768⟩, ⟨117890216084, 127382116622⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 173015040 174325760 265093120 270663680 ⟨⟨125962156526, 125962156528⟩, ⟨121206966700, 130792083675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 265093120 270663680 ⟨⟨124976279980, 124976279987⟩, ⟨120249981756, 129776664455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 175636480 176947200 259522560 265093120 ⟨⟨121635661347, 121635661354⟩, ⟨116955377105, 126389526767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 176947200 178257920 259522560 265093120 ⟨⟨120679083664, 120679083672⟩, ⟨116027042263, 125404065134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 175636480 176947200 265093120 270663680 ⟨⟨123997367387, 123997367394⟩, ⟨119299649746, 128768529046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 176947200 178257920 265093120 270663680 ⟨⟨123025311095, 123025311102⟩, ⟨118355868242, 127767564417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 174325760 270663680 276234240 ⟨⟨128347336192, 128347336198⟩, ⟨123574762072, 133194492905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 174325760 175636480 270663680 276234240 ⟨⟨127346043156, 127346043165⟩, ⟨122602386166, 132163639650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 173015040 174325760 276234240 281804800 ⟨⟨130724999249, 130724999254⟩, ⟨125935146569, 135589277996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 174325760 175636480 276234240 281804800 ⟨⟨129708438365, 129708438374⟩, ⟨124947525666, 134543142032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 175636480 176947200 270663680 276234240 ⟨⟨126351756144, 126351756153⟩, ⟨121636707184, 131140110150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 176947200 178257920 270663680 276234240 ⟨⟨125364367474, 125364367483⟩, ⟨120677622592, 130123791420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 175636480 176947200 276234240 281804800 ⟨⟨128698923080, 128698923089⟩, ⟨123966643214, 133504367230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 176947200 178257920 276234240 281804800 ⟨⟨127696345717, 127696345725⟩, ⟨122992396623, 132472840680⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 259522560 281804800 t = true :=
  ⟨_, (join_sr (m := 270663680) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 265093120) (by decide) (join_su (m := 174325760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 174325760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 265093120) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 176947200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 175636480) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 174325760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 174325760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 276234240) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 176947200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
