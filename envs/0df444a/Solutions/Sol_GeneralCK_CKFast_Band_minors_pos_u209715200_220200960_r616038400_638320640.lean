-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r616038400_638320640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:58:21.967544+00:00
-- url     : https://prove2.me/submissions/e8d75502-3f26-409a-9efa-78e5e7b7b4b5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [47/64, 487/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 616038400 621608960 ⟨⟨217368592217, 217368592226⟩, ⟨208812163783, 226090720005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 212336640 621608960 627179520 ⟨⟨219144558114, 219144558123⟩, ⟨210561191221, 227893497752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 214958080 616038400 621608960 ⟨⟨214200326115, 214200326124⟩, ⟨205711216626, 222854391853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 621608960 627179520 ⟨⟨215955325465, 215955325474⟩, ⟨207439268034, 224636237910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 212336640 627179520 632750080 ⟨⟨220918604543, 220918604551⟩, ⟨212308324819, 229694325604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 212336640 632750080 638320640 ⟨⟨222690758934, 222690758943⟩, ⟨214053591513, 231493231472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 214958080 627179520 632750080 ⟨⟨217708476493, 217708476501⟩, ⟨209165494591, 226416207472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212336640 214958080 632750080 638320640 ⟨⟨219459805457, 219459805466⟩, ⟨210889922092, 228194327247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 616038400 621608960 ⟨⟨211050933898, 211050933903⟩, ⟨202628443943, 219637633941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 217579520 621608960 627179520 ⟨⟨212784889259, 212784889264⟩, ⟨204335451750, 221398460256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 616038400 621608960 ⟨⟨207919999092, 207919999102⟩, ⟨199563442359, 216440017069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 220200960 621608960 627179520 ⟨⟨209632835943, 209632835952⟩, ⟨201249341628, 218179738814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214958080 217579520 627179520 632750080 ⟨⟨214517065738, 214517065741⟩, ⟨206040702027, 223157481735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214958080 217579520 632750080 638320640 ⟨⟨216247488459, 216247488463⟩, ⟨207744219457, 224914723926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 220200960 627179520 632750080 ⟨⟨211343961654, 211343961661⟩, ⟨202933549020, 219917725654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217579520 220200960 632750080 638320640 ⟨⟨213053400254, 213053400263⟩, ⟨204616088154, 221654002019⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 616038400 638320640 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 627179520) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 621608960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 621608960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212336640) (by decide) (join_sr (m := 632750080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 632750080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 627179520) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 621608960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 621608960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 217579520) (by decide) (join_sr (m := 632750080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 632750080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (47/64 : ℝ) (487/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  have e3 : (((638320640 : ℤ) : ℝ) / (D : ℝ)) = (487/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
