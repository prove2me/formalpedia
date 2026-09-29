-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u201850880_204472320_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:41:03.224967+00:00
-- url     : https://prove2.me/submissions/1fe498fc-29d6-4a11-8dc9-36055ed79ce2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [77/320, 39/160]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 201850880 202506240 131399680 132792320 ⟨⟨54106165999, 54106166006⟩, ⟨52532253725, 55690583121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 202506240 132792320 134184960 ⟨⟨54655485912, 54655485917⟩, ⟨53079518454, 56241961729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 202506240 203161600 131399680 132792320 ⟨⟨53872868319, 53872868326⟩, ⟨52302769216, 55453428607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 202506240 203161600 132792320 134184960 ⟨⟨54419984205, 54419984211⟩, ⟨52847835598, 56002597574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 202506240 134184960 135577600 ⟨⟨55204405848, 55204405854⟩, ⟨53626385025, 56792938523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201850880 202506240 135577600 136970240 ⟨⟨55752926961, 55752926967⟩, ⟨54172854581, 57343514663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 202506240 203161600 134184960 135577600 ⟨⟨54966704796, 54966704803⟩, ⟨53392508468, 56551369445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 202506240 203161600 135577600 136970240 ⟨⟨55513031231, 55513031236⟩, ⟨53936788956, 57099745360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 203161600 203816960 131399680 132792320 ⟨⟨53640426714, 53640426721⟩, ⟨52074119082, 55217152205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 203161600 203816960 132792320 134184960 ⟨⟨54185344760, 54185344767⟩, ⟨52616993292, 55764117729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203816960 204472320 131399680 132792320 ⟨⟨53408834162, 53408834169⟩, ⟨51846296485, 54981746703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 203816960 204472320 132792320 134184960 ⟨⟨53951560515, 53951560521⟩, ⟨52386984658, 55526514940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 203161600 203816960 134184960 135577600 ⟨⟨54729872147, 54729872153⟩, ⟨53159478589, 56310690823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203161600 203816960 135577600 136970240 ⟨⟨55274009991, 55274009997⟩, ⟨53701576086, 56856872614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203816960 204472320 134184960 135577600 ⟨⟨54493900794, 54493900800⟩, ⟨52927288471, 56070895366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203816960 204472320 135577600 136970240 ⟨⟨55035856098, 55035856104⟩, ⟨53467209018, 56614889091⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 201850880 204472320 131399680 136970240 t = true :=
  ⟨_, (join_su (m := 203161600) (by decide) (join_sr (m := 134184960) (by decide) (join_su (m := 202506240) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 132792320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 202506240) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 135577600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 134184960) (by decide) (join_su (m := 203816960) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 132792320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 203816960) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 135577600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (77/320 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
