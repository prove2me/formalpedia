-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_153354240_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:01:24.040539+00:00
-- url     : https://prove2.me/submissions/7afb25b1-a930-4274-b96f-0747e5032042

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 117/640]`, `ρ ∈ [1/10, 137/1280]` by 13 cells of the computing
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
theorem cell0 : cellOK 152043520 152371200 83886080 85360640 ⟨⟨49293809348, 49293809355⟩, ⟨48110552876, 50483369019⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 152371200 152698880 83886080 85360640 ⟨⟨49181869209, 49181869215⟩, ⟨48000758739, 50369262009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 152371200 85360640 86835200 ⟨⟨50113492755, 50113492763⟩, ⟨48928559786, 51304724506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 152371200 152698880 85360640 86835200 ⟨⟨49999844108, 49999844115⟩, ⟨48817060206, 51188905980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152698880 153026560 83886080 85360640 ⟨⟨49070248821, 49070248827⟩, ⟨47891276427, 50255482782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 153026560 153354240 83886080 85360640 ⟨⟨48958946475, 48958946480⟩, ⟨47782104284, 50142029583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 152698880 153026560 85360640 86835200 ⟨⟨49886519208, 49886519215⟩, ⟨48705876444, 51073419241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 153026560 153354240 85360640 86835200 ⟨⟨49773516331, 49773516336⟩, ⟨48595006825, 50958262512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 152043520 152698880 86835200 88309760 ⟨⟨50874232283, 50874232286⟩, ⟨48985730845, 52778539636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 152043520 152698880 88309760 89784320 ⟨⟨51690617858, 51690617862⟩, ⟨49799209310, 53597826511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 152698880 153026560 86835200 88309760 ⟨⟨50701576218, 50701576225⟩, ⟨49519268821, 51890136568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 153026560 153354240 86835200 88309760 ⟨⟨50586879988, 50586879992⟩, ⟨49406708860, 51773283530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152698880 153354240 88309760 89784320 ⟨⟨51457192811, 51457192819⟩, ⟨49571926193, 53358164856⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 153354240 83886080 89784320 t = true :=
  ⟨_, (join_sr (m := 86835200) (by decide) (join_su (m := 152698880) (by decide) (join_sr (m := 85360640) (by decide) (join_su (m := 152371200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 152371200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 85360640) (by decide) (join_su (m := 153026560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 153026560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 152698880) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 88309760) (by decide) (join_su (m := 153026560) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (117/640 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((153354240 : ℤ) : ℝ) / (D : ℝ)) = (117/640 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
