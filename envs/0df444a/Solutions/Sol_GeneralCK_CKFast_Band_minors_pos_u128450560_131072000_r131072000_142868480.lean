-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u128450560_131072000_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:25:00.69304+00:00
-- url     : https://prove2.me/submissions/51644994-4166-4251-a9b4-b15b51161235

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [49/320, 5/32]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 128450560 129105920 131072000 134021120 ⟨⟨88323056506, 88323056515⟩, ⟨85495419771, 91181861296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 129105920 129761280 131072000 134021120 ⟨⟨87921166439, 87921166442⟩, ⟨85105164369, 90768116736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 128450560 129105920 134021120 136970240 ⟨⟨90115418558, 90115418567⟩, ⟨87281336399, 92980581675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 129105920 129761280 134021120 136970240 ⟨⟨89706685357, 89706685361⟩, ⟨86884246574, 92559987082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 129761280 130416640 131072000 134021120 ⟨⟨87521774182, 87521774191⟩, ⟨84717310957, 90356968268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 130416640 131072000 131072000 134021120 ⟨⟨87124851612, 87124851620⟩, ⟨84331832619, 89948386503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 129761280 130416640 134021120 136970240 ⟨⟨89300477693, 89300477702⟩, ⟨86489586728, 92142016012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 130416640 131072000 134021120 136970240 ⟨⟨88896767260, 88896767269⟩, ⟨86097329757, 91726638900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 128450560 129105920 136970240 139919360 ⟨⟨91901446024, 91901446031⟩, ⟨89060981009, 94772904793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 129105920 129761280 136970240 139919360 ⟨⟨91485940381, 91485940383⟩, ⟨88657126605, 94345531701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 128450560 129105920 139919360 142868480 ⟨⟨93681202780, 93681202787⟩, ⟨90834416535, 96558895482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 129105920 129761280 139919360 142868480 ⟨⟨93258994348, 93258994352⟩, ⟨90423866380, 96124814365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 129761280 130416640 136970240 139919360 ⟨⟨91072987182, 91072987190⟩, ⟨88255729363, 93920808731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 130416640 131072000 136970240 139919360 ⟨⟨90662557951, 90662557958⟩, ⟨87856761999, 93498706155⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 129761280 130416640 139919360 142868480 ⟨⟨92839364469, 92839364476⟩, ⟨90015799778, 95693409158⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 130416640 131072000 139919360 142868480 ⟨⟨92422284500, 92422284507⟩, ⟨89610189275, 95264649981⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 128450560 131072000 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 129761280) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 129105920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 129105920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 130416640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 130416640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 129761280) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 129105920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 129105920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 130416640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 130416640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (49/320 : ℝ) (5/32 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((128450560 : ℤ) : ℝ) / (D : ℝ)) = (49/320 : ℝ) := by norm_num [D]
  have e1 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
