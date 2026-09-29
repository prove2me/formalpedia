-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r616038400_638320640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:59:19.525227+00:00
-- url     : https://prove2.me/submissions/43bfd66d-03b9-42fd-ac27-148c5c6df4ae

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [47/64, 487/640]` by 19 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 616038400 621608960 ⟨⟨204807114517, 204807114526⟩, ⟨196515817473, 213261121606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 621608960 627179520 ⟨⟨206498761146, 206498761154⟩, ⟨198180545786, 214979657062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 616038400 621608960 ⟨⟨201711881924, 201711881933⟩, ⟨193485183511, 210100537150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 621608960 627179520 ⟨⟨203382269325, 203382269334⟩, ⟨195128680888, 211797807597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 627179520 632750080 ⟨⟨208188762693, 208188762700⟩, ⟨199843646234, 216696525828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 632750080 638320640 ⟨⟨209877142130, 209877142139⟩, ⟨201505141403, 218411751248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 627179520 632750080 ⟨⟨205051076035, 205051076043⟩, ⟨196770612778, 213493477862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 632750080 638320640 ⟨⟨206718324001, 206718324010⟩, ⟨198411000774, 215187570240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 616038400 621608960 ⟨⟨198633911696, 198633911705⟩, ⟨190471163042, 206957862200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 621608960 627179520 ⟨⟨200282973474, 200282973483⟩, ⟨192093371842, 208633791807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 229376000 616038400 621608960 ⟨⟨196336532773, 196336532782⟩, ⟨191655067509, 201072366724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229376000 230686720 616038400 621608960 ⟨⟨194810143996, 194810144005⟩, ⟨190150278062, 199524191280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228065280 229376000 621608960 627179520 ⟨⟨197969558275, 197969558283⟩, ⟨193273949686, 202719512848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229376000 230686720 621608960 627179520 ⟨⟨196432459191, 196432459200⟩, ⟨191758463066, 201160617673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 225443840 228065280 627179520 632750080 ⟨⟨201930517292, 201930517299⟩, ⟨193714075919, 210308186045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 225443840 228065280 632750080 638320640 ⟨⟨203576564111, 203576564120⟩, ⟨195333295905, 211981066195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 228065280 229376000 627179520 632750080 ⟨⟨199601111788, 199601111795⟩, ⟨194891369883, 204365175762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 229376000 230686720 627179520 632750080 ⟨⟨198053332535, 198053332542⟩, ⟨193365215671, 202795591563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 228065280 230686720 632750080 638320640 ⟨⟨200451488745, 200451488749⟩, ⟨192271664217, 208791854583⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 616038400 638320640 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 627179520) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 621608960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 621608960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 632750080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 632750080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 627179520) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 621608960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 621608960) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 229376000) (by decide) (leaf_ok cell12) (leaf_ok cell13)))) (join_su (m := 228065280) (by decide) (join_sr (m := 632750080) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 632750080) (by decide) (join_su (m := 229376000) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (47/64 : ℝ) (487/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  have e3 : (((638320640 : ℤ) : ℝ) / (D : ℝ)) = (487/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
