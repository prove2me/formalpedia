-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u245104640_246415360_r125829120_128614400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:28:34.75547+00:00
-- url     : https://prove2.me/submissions/3eab34d6-e300-4c09-8a20-1e3c48ba7b4f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [187/640, 47/160]`, `ρ ∈ [3/20, 157/1024]` by 14 cells of the computing
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
theorem cell0 : cellOK 245104640 245432320 125829120 126525440 ⟨⟨38545005411, 38545005417⟩, ⟨37866484771, 39225574021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 245104640 245432320 126525440 127221760 ⟨⟨38753357914, 38753357919⟩, ⟨38074409661, 39434354901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 245432320 245760000 125829120 126525440 ⟨⟨38454278657, 38454278662⟩, ⟨37776431253, 39134170595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 245432320 245760000 126525440 127221760 ⟨⟨38662160001, 38662160006⟩, ⟨37983885601, 39342479701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245104640 245432320 127221760 128614400 ⟨⟨39065803005, 39065803010⟩, ⟨38270936432, 39863592601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245432320 245760000 127221760 128614400 ⟨⟨38973898909, 38973898914⟩, ⟨38180001103, 39770713893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245760000 246087680 125829120 126525440 ⟨⟨38363675797, 38363675803⟩, ⟨37686500006, 39042892698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245760000 246087680 126525440 127221760 ⟨⟨38571086500, 38571086505⟩, ⟨37893484328, 39250730548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246087680 246415360 125829120 126525440 ⟨⟨38273196362, 38273196367⟩, ⟨37596690568, 38951739854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 246087680 246415360 126525440 127221760 ⟨⟨38480136939, 38480136944⟩, ⟨37803205379, 39159106964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245760000 246087680 127221760 127918080 ⟨⟨38778453165, 38778453170⟩, ⟨38100424648, 39458524324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245760000 246087680 127918080 128614400 ⟨⟨38985775841, 38985775847⟩, ⟨38307321013, 39666274078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 246087680 246415360 127221760 127918080 ⟨⟨38687033771, 38687033776⟩, ⟨38009676480, 39366430296⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 246087680 246415360 127918080 128614400 ⟨⟨38893886907, 38893886913⟩, ⟨38216103918, 39573709897⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 245104640 246415360 125829120 128614400 t = true :=
  ⟨_, (join_su (m := 245760000) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 245432320) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126525440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 245432320) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 127221760) (by decide) (join_su (m := 246087680) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 126525440) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 246087680) (by decide) (join_sr (m := 127918080) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 127918080) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (187/640 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (157/1024 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((128614400 : ℤ) : ℝ) / (D : ℝ)) = (157/1024 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
