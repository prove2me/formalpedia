-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_37748736_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:37:30.69145+00:00
-- url     : https://prove2.me/submissions/3249d45e-4d32-488f-bfbd-7f4a73ecc0c3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 9/200]`, `ρ ∈ [303/2560, 17/128]` by 13 cells of the computing
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
theorem cell0 : cellOK 33554432 34603008 99287040 102318080 ⟨⟨170214388685, 170214388705⟩, ⟨160541939052, 180202157802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 33554432 34603008 102318080 105349120 ⟨⟨173869685286, 173869685302⟩, ⟨164214062768, 183834900445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 34603008 35651584 99287040 102318080 ⟨⟨167635095924, 167635095940⟩, ⟨158143960227, 177431694871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 34603008 35651584 102318080 105349120 ⟨⟨171265479639, 171265479655⟩, ⟨161789087011, 181041932845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 33554432 34603008 105349120 111411200 ⟨⟨179254864838, 179254864858⟩, ⟨166067818959, 193002861128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 34603008 35651584 105349120 111411200 ⟨⟨176615713927, 176615713947⟩, ⟨163672858371, 190102351580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 35651584 36700160 99287040 102318080 ⟨⟨165134961965, 165134961980⟩, ⟨155818116207, 174747892218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 35651584 36700160 102318080 105349120 ⟨⟨168740214209, 168740214224⟩, ⟨159436182303, 178335229394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 36700160 37748736 99287040 102318080 ⟨⟨162710105371, 162710105390⟩, ⟨153560927267, 172146436040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 36700160 37748736 102318080 105349120 ⟨⟨166290059128, 166290059143⟩, ⟨157151907711, 175710542559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 35651584 36700160 105349120 111411200 ⟨⟨174055112942, 174055112961⟩, ⟨161347376256, 187290264188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 36700160 37748736 105349120 108380160 ⟨⟨169821406114, 169821406133⟩, ⟨160694891798, 179225537386⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 36700160 37748736 108380160 111411200 ⟨⟨173305603644, 173305603663⟩, ⟨164191290100, 182692921906⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 37748736 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 35651584) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 34603008) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 102318080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 34603008) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 105349120) (by decide) (join_su (m := 36700160) (by decide) (join_sr (m := 102318080) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 102318080) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 36700160) (by decide) (leaf_ok cell10) (join_sr (m := 108380160) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (9/200 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
