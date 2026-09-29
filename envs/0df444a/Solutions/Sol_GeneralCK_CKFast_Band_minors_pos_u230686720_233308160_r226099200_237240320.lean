-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:31:56.713314+00:00
-- url     : https://prove2.me/submissions/ab7f7abe-5086-4a63-97c6-4df29f0ebfc7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 226099200 228884480 ⟨⟨75405345753, 75405345757⟩, ⟨73590745367, 77233047342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 231342080 231997440 226099200 228884480 ⟨⟨75075517329, 75075517335⟩, ⟨73265571704, 76898514632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 230686720 231342080 228884480 231669760 ⟨⟨76290973511, 76290973515⟩, ⟨74472538858, 78122516919⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 228884480 231669760 ⟨⟨75957577472, 75957577479⟩, ⟨74143807004, 77784407311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 231997440 232652800 226099200 228884480 ⟨⟨74746543728, 74746543734⟩, ⟨72941232445, 76564857458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 232652800 233308160 226099200 228884480 ⟨⟨74418418852, 74418418857⟩, ⟨72617721635, 76232069575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231997440 232652800 228884480 231669760 ⟨⟨75625041798, 75625041804⟩, ⟨73815915102, 77447178772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 232652800 233308160 228884480 231669760 ⟨⟨75293360364, 75293360370⟩, ⟨73488857173, 77110825029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 230686720 231342080 231669760 234455040 ⟨⟨77175812434, 77175812436⟩, ⟨75353546802, 79011194304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231342080 231997440 231669760 234455040 ⟨⟨76838858276, 76838858281⟩, ⟨75021266172, 78669517376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 230686720 231342080 234455040 237240320 ⟨⟨78059866444, 78059866449⟩, ⟨76233773105, 79899083447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 231342080 231997440 234455040 237240320 ⟨⟨77719363606, 77719363611⟩, ⟨75897953056, 79553848716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 232652800 231669760 234455040 ⟨⟨76502769932, 76502769938⟩, ⟨74689830952, 78328726956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 232652800 233308160 231669760 234455040 ⟨⟨76167541253, 76167541259⟩, ⟨74359235138, 77988816747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 231997440 232652800 234455040 237240320 ⟨⟨77379731940, 77379731946⟩, ⟨75562983786, 79209505840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232652800 233308160 234455040 237240320 ⟨⟨77040965272, 77040965279⟩, ⟨75228859267, 78866048499⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 231997440) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 231342080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 231342080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 232652800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 232652800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 231997440) (by decide) (join_sr (m := 234455040) (by decide) (join_su (m := 231342080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 231342080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 234455040) (by decide) (join_su (m := 232652800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 232652800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
