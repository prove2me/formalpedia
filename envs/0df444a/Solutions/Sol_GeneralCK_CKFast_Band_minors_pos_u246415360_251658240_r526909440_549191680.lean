-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r526909440_549191680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:34:52.292163+00:00
-- url     : https://prove2.me/submissions/2799a49f-a041-4b30-90a8-b48f41b21a6e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [201/320, 419/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 526909440 532480000 ⟨⟨151455878734, 151455878742⟩, ⟨147289512781, 155673488225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247726080 249036800 526909440 532480000 ⟨⟨150160988075, 150160988083⟩, ⟨146014271925, 154358717952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247726080 532480000 538050560 ⟨⟨152957067683, 152957067691⟩, ⟨148776786280, 157188631320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 532480000 538050560 ⟨⟨151650832378, 151650832386⟩, ⟨147490237748, 155862482028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 250347520 526909440 532480000 ⟨⟨148869730466, 148869730474⟩, ⟨144742554079, 153047691797⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250347520 251658240 526909440 532480000 ⟨⟨147582062965, 147582062973⟩, ⟨143474317350, 151740365770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249036800 250347520 532480000 538050560 ⟨⟨150348225506, 150348225514⟩, ⟨146207208462, 154540071331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 250347520 251658240 532480000 538050560 ⟨⟨149049204298, 149049204305⟩, ⟨144927656684, 153221355425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247726080 538050560 543621120 ⟨⟨154456930862, 154456930870⟩, ⟨150262738908, 158702442833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 249036800 538050560 543621120 ⟨⟨153139381724, 153139381731⟩, ⟨148964912969, 157364945898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247726080 543621120 549191680 ⟨⟨155955483780, 155955483788⟩, ⟨151747386048, 160214938404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247726080 249036800 543621120 549191680 ⟨⟨154626651218, 154626651226⟩, ⟨150438312574, 158866124789⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 538050560 543621120 ⟨⟨151825455909, 151825455917⟩, ⟨147670602033, 156031181528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251658240 538050560 543621120 ⟨⟨150515110820, 150515110828⟩, ⟨146379764512, 154701106115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 249036800 250347520 543621120 549191680 ⟨⟨153301436382, 153301436389⟩, ⟨149132749379, 157521037215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 543621120 549191680 ⟨⟨151979796853, 151979796860⟩, ⟨147830655038, 156179632267⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 526909440 549191680 t = true :=
  ⟨_, (join_sr (m := 538050560) (by decide) (join_su (m := 249036800) (by decide) (join_sr (m := 532480000) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 247726080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 532480000) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 250347520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 249036800) (by decide) (join_sr (m := 543621120) (by decide) (join_su (m := 247726080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 247726080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 543621120) (by decide) (join_su (m := 250347520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 250347520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (201/320 : ℝ) (419/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  have e3 : (((549191680 : ℤ) : ℝ) / (D : ℝ)) = (419/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
