-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r504627200_526909440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:04:20.028973+00:00
-- url     : https://prove2.me/submissions/68c5781a-267e-400c-8102-b566c72da608

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [77/128, 201/320]` by 11 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 504627200 515768320 ⟨⟨229360750968, 229360750977⟩, ⟨218362697377, 240629337658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 170393600 173015040 504627200 515768320 ⟨⟨226222333394, 226222333403⟩, ⟨215338820771, 237373853782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 170393600 515768320 526909440 ⟨⟨233703229243, 233703229252⟩, ⟨222649246249, 245025757896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 515768320 526909440 ⟨⟨230521796271, 230521796281⟩, ⟨219581929392, 241727809684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 175636480 504627200 510197760 ⟨⟨222046755744, 222046755754⟩, ⟨212991589500, 231287729531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 173015040 175636480 510197760 515768320 ⟨⟨224179040775, 224179040786⟩, ⟨215096908691, 233446516611⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 175636480 178257920 504627200 510197760 ⟨⟨218977555031, 218977555035⟩, ⟨210004223126, 228135286287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 175636480 178257920 510197760 515768320 ⟨⟨221088002660, 221088002667⟩, ⟨212087576649, 230272402403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 175636480 515768320 526909440 ⟨⟨227369672663, 227369672673⟩, ⟨216542267979, 238460840103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 175636480 178257920 515768320 521338880 ⟨⟨223194420638, 223194420641⟩, ⟨214166978035, 232405406032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 178257920 521338880 526909440 ⟨⟨225296865112, 225296865118⟩, ⟨216242482195, 234534354575⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 504627200 526909440 t = true :=
  ⟨_, (join_su (m := 173015040) (by decide) (join_sr (m := 515768320) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 170393600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 515768320) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 510197760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 510197760) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 175636480) (by decide) (leaf_ok cell8) (join_sr (m := 521338880) (by decide) (leaf_ok cell9) (leaf_ok cell10)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (77/128 : ℝ) (201/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  have e3 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
