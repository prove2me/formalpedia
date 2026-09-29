-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r370933760_382074880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:02:52.046068+00:00
-- url     : https://prove2.me/submissions/09ec7cc2-f64e-49a9-864b-9c9d7bc888c8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [283/640, 583/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 370933760 373719040 ⟨⟨108432227692, 108432227698⟩, ⟨105153272791, 111747465224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247726080 373719040 376504320 ⟨⟨109205154408, 109205154415⟩, ⟨105919564585, 112527063294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 249036800 370933760 373719040 ⟨⟨107472357205, 107472357211⟩, ⟨104206631107, 110774194654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 373719040 376504320 ⟨⟨108239079709, 108239079715⟩, ⟨104966741858, 111547566029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247726080 376504320 379289600 ⟨⟨109977628912, 109977628919⟩, ⟨106685405211, 113306207946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247726080 379289600 382074880 ⟨⟨110749653477, 110749653484⟩, ⟨107450796933, 114084901462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 249036800 376504320 379289600 ⟨⟨109005361008, 109005361013⟩, ⟨105726412300, 112320495145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247726080 249036800 379289600 382074880 ⟨⟨109771203310, 109771203316⟩, ⟨106485644634, 113092984219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 250347520 370933760 373719040 ⟨⟨106516006705, 106516006711⟩, ⟨103263411768, 109804543243⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249036800 250347520 373719040 376504320 ⟨⟨107276531769, 107276531776⟩, ⟨104017348461, 110571694468⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251658240 370933760 373719040 ⟨⟨105563130953, 105563130959⟩, ⟨102323570687, 108838464582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250347520 251658240 373719040 376504320 ⟨⟨106317465338, 106317465345⟩, ⟨103071340287, 109599402197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 376504320 379289600 ⟨⟨108036626439, 108036626446⟩, ⟨104770855511, 111338414393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 249036800 250347520 379289600 382074880 ⟨⟨108796292860, 108796292866⟩, ⟨105523935052, 112104705174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251658240 376504320 379289600 ⟨⟨107071379945, 107071379951⟩, ⟨103818690716, 110359919273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 379289600 382074880 ⟨⟨107824876854, 107824876861⟩, ⟨104565624051, 111120017901⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 370933760 382074880 t = true :=
  ⟨_, (join_su (m := 249036800) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 373719040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 373719040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247726080) (by decide) (join_sr (m := 379289600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 379289600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 376504320) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 373719040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 373719040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 250347520) (by decide) (join_sr (m := 379289600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 379289600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (583/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((382074880 : ℤ) : ℝ) / (D : ℝ)) = (583/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
