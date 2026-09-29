-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r526909440_549191680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:46:18.689025+00:00
-- url     : https://prove2.me/submissions/3a1783f5-8273-4f2b-a32d-215c1572541c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [201/320, 419/640]` by 13 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 526909440 532480000 ⟨⟨183743337447, 183743337455⟩, ⟨179069401249, 188474346600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 216268800 217579520 526909440 532480000 ⟨⟨182347081548, 182347081557⟩, ⟨177695786695, 187055194332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 217579520 532480000 538050560 ⟨⟨184810568993, 184810568998⟩, ⟨176795157770, 192990796510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 217579520 218890240 526909440 532480000 ⟨⟨180955643533, 180955643541⟩, ⟨176326850494, 185641000534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 218890240 220200960 526909440 532480000 ⟨⟨179568967208, 179568967212⟩, ⟨174962537868, 184231707593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 217579520 218890240 532480000 538050560 ⟨⟨182704842358, 182704842367⟩, ⟨178061575760, 187404638985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 218890240 220200960 532480000 538050560 ⟨⟨181306975897, 181306975901⟩, ⟨176686086117, 185984146809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214958080 217579520 538050560 543621120 ⟨⟨186574331170, 186574331174⟩, ⟨178531598309, 194781871128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 543621120 549191680 ⟨⟨188335918094, 188335918096⟩, ⟨180265891747, 196570737929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217579520 218890240 538050560 543621120 ⟨⟨184451903410, 184451903418⟩, ⟨179794182506, 189166119132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 220200960 538050560 543621120 ⟨⟨183042889614, 183042889618⟩, ⟨178407557900, 187734471284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 218890240 543621120 549191680 ⟨⟨186196853558, 186196853566⟩, ⟨181524697299, 190925468141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 218890240 220200960 543621120 549191680 ⟨⟨184776734602, 184776734604⟩, ⟨180126979164, 189482707549⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 526909440 549191680 t = true :=
  ⟨_, (join_sr (m := 538050560) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 532480000) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 532480000) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 218890240) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 217579520) (by decide) (join_sr (m := 543621120) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 543621120) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 218890240) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (201/320 : ℝ) (419/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  have e3 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
