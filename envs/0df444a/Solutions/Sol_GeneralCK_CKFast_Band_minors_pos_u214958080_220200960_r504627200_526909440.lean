-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r504627200_526909440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:40:09.554252+00:00
-- url     : https://prove2.me/submissions/7050749b-7a5f-4b92-9d74-256852afe849

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [77/128, 201/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 504627200 510197760 ⟨⟨176634319945, 176634319954⟩, ⟨172018580881, 181307287757⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 216268800 217579520 504627200 510197760 ⟨⟨175283196963, 175283196970⟩, ⟨170690049823, 179933301268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 216268800 510197760 515768320 ⟨⟨178415055112, 178415055120⟩, ⟨173784733963, 183102568009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 510197760 515768320 ⟨⟨177052579563, 177052579571⟩, ⟨172444863896, 181717219515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 217579520 218890240 504627200 510197760 ⟨⟨173936926691, 173936926699⟩, ⟨169366226517, 178564313817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 218890240 220200960 504627200 510197760 ⟨⟨172595451752, 172595451756⟩, ⟨168047055115, 177200266492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 217579520 218890240 510197760 515768320 ⟨⟨175694948978, 175694948987⟩, ⟨171109695178, 180336860890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 218890240 220200960 510197760 515768320 ⟨⟨174342106268, 174342106272⟩, ⟨169779172220, 178961433539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 216268800 515768320 521338880 ⟨⟨180193450477, 180193450484⟩, ⟨175548569332, 184895485072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 216268800 217579520 515768320 521338880 ⟨⟨178819669041, 178819669048⟩, ⟨174197406125, 183498822076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 216268800 521338880 526909440 ⟨⟨181969535002, 181969535010⟩, ⟨177310115618, 186686068240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 216268800 217579520 521338880 526909440 ⟨⟨180584493675, 180584493682⟩, ⟨175947704471, 185278137547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 515768320 521338880 ⟨⟨177450724171, 177450724180⟩, ⟨172850937224, 182107139120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 218890240 220200960 515768320 521338880 ⟨⟨176086559077, 176086559080⟩, ⟨171509107306, 180720377935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 218890240 521338880 526909440 ⟨⟨179204279882, 179204279891⟩, ⟨174589979958, 183875176425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218890240 220200960 521338880 526909440 ⟨⟨177828837132, 177828837136⟩, ⟨173236887030, 182477126930⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 504627200 526909440 t = true :=
  ⟨_, (join_sr (m := 515768320) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 510197760) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 216268800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 510197760) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 218890240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 217579520) (by decide) (join_sr (m := 521338880) (by decide) (join_su (m := 216268800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 216268800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 521338880) (by decide) (join_su (m := 218890240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 218890240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (77/128 : ℝ) (201/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((504627200 : ℤ) : ℝ) / (D : ℝ)) = (77/128 : ℝ) := by norm_num [D]
  have e3 : (((526909440 : ℤ) : ℝ) / (D : ℝ)) = (201/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
