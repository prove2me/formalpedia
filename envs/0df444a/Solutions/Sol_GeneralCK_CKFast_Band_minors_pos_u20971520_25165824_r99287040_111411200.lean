-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r99287040_111411200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:19:28.922707+00:00
-- url     : https://prove2.me/submissions/a28f1a82-d68a-4f29-b3c3-a31cf38ba79e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/40, 3/100]`, `ρ ∈ [303/2560, 17/128]` by 8 cells of the computing
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
theorem cell0 : cellOK 20971520 22020096 99287040 105349120 ⟨⟨211205978007, 211205978032⟩, ⟨193949508805, 229364083211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 22020096 23068672 99287040 105349120 ⟨⟨207226937453, 207226937478⟩, ⟨190398130831, 224921530843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 20971520 22020096 105349120 111411200 ⟨⟨218878078557, 218878078582⟩, ⟨201801019778, 236809860485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 22020096 23068672 105349120 111411200 ⟨⟨214872846260, 214872846280⟩, ⟨198207908018, 232359801280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 23068672 24117248 99287040 105349120 ⟨⟨203406072865, 203406072884⟩, ⟨186983711731, 220660523646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 24117248 25165824 99287040 105349120 ⟨⟨199733291033, 199733291052⟩, ⟨183697723956, 216569233157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 23068672 24117248 105349120 111411200 ⟨⟨211022341224, 211022341244⟩, ⟨194749612592, 228086267921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 24117248 25165824 105349120 111411200 ⟨⟨207316915094, 207316915113⟩, ⟨191417921990, 223978032515⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 20971520 25165824 99287040 111411200 t = true :=
  ⟨_, (join_su (m := 23068672) (by decide) (join_sr (m := 105349120) (by decide) (join_su (m := 22020096) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 22020096) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 105349120) (by decide) (join_su (m := 24117248) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 24117248) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/40 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((20971520 : ℤ) : ℝ) / (D : ℝ)) = (1/40 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  have e3 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
