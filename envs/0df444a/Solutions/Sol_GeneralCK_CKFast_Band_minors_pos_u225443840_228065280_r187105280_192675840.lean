-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u225443840_228065280_r187105280_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:56:55.680997+00:00
-- url     : https://prove2.me/submissions/6b1e8efc-350c-4ff8-94ce-8ae9ed6c5f05

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/160, 87/320]`, `ρ ∈ [571/2560, 147/640]` by 11 cells of the computing
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
theorem cell0 : cellOK 225443840 226099200 187105280 189890560 ⟨⟨65180606369, 65180606374⟩, ⟨63383174787, 66991450061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 226099200 226754560 187105280 188497920 ⟨⟨64664455559, 64664455564⟩, ⟨63144974217, 66193226678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 226099200 226754560 188497920 189890560 ⟨⟨65126306016, 65126306022⟩, ⟨63605001821, 66656904744⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 225443840 226099200 189890560 192675840 ⟨⟨66107608791, 66107608797⟩, ⟨64306209908, 67922427130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 226099200 226754560 189890560 192675840 ⟨⟨65818648477, 65818648483⟩, ⟨64021943348, 67628719076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 226754560 227409920 187105280 188497920 ⟨⟨64381013719, 64381013725⟩, ⟨62864845010, 65906440465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 226754560 227409920 188497920 189890560 ⟨⟨64840983168, 64840983174⟩, ⟨63322996033, 66368233139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 227409920 228065280 187105280 188497920 ⟨⟨64098378000, 64098378001⟩, ⟨62585505600, 65620476901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 227409920 228065280 188497920 189890560 ⟨⟨64556470062, 64556470065⟩, ⟨63041783659, 66080387807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 226754560 227409920 189890560 192675840 ⟨⟨65530509348, 65530509354⟩, ⟨63738476285, 67335854242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 227409920 228065280 189890560 192675840 ⟨⟨65243185344, 65243185345⟩, ⟨63455802821, 67043826398⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 225443840 228065280 187105280 192675840 t = true :=
  ⟨_, (join_su (m := 226754560) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 226099200) (by decide) (leaf_ok cell0) (join_sr (m := 188497920) (by decide) (leaf_ok cell1) (leaf_ok cell2))) (join_su (m := 226099200) (by decide) (leaf_ok cell3) (leaf_ok cell4))) (join_sr (m := 189890560) (by decide) (join_su (m := 227409920) (by decide) (join_sr (m := 188497920) (by decide) (leaf_ok cell5) (leaf_ok cell6)) (join_sr (m := 188497920) (by decide) (leaf_ok cell7) (leaf_ok cell8))) (join_su (m := 227409920) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/160 : ℝ) (87/320 : ℝ) →
    rho ∈ Set.Icc (571/2560 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e1 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e2 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
