-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_159907840_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:44:54.367826+00:00
-- url     : https://prove2.me/submissions/e92d245c-cd06-4c18-890e-ac3d65df1ec5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 61/320]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 157941760 154664960 157614080 ⟨⟨84694847607, 84694847615⟩, ⟨82255996312, 87156841790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157941760 158597120 154664960 157614080 ⟨⟨84335832026, 84335832033⟩, ⟨81905434282, 86789239663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 157941760 157614080 160563200 ⟨⟨86179911771, 86179911779⟩, ⟨83735424177, 88647508902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 157941760 158597120 157614080 160563200 ⟨⟨85815443485, 85815443493⟩, ⟨83379420603, 88274443734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 158597120 159252480 154664960 157614080 ⟨⟨83978542146, 83978542149⟩, ⟨81556541417, 86423420981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 159252480 159907840 154664960 157614080 ⟨⟨83622961740, 83622961746⟩, ⟨81209302085, 86059368913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 158597120 159252480 157614080 160563200 ⟨⟨85452717955, 85452717959⟩, ⟨83025103345, 87903178954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159252480 159907840 157614080 160563200 ⟨⟨85091718854, 85091718862⟩, ⟨82672456668, 87533697638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 157941760 160563200 163512320 ⟨⟨87661344387, 87661344395⟩, ⟨85211251412, 90134513374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 157941760 158597120 160563200 163512320 ⟨⟨87291462676, 87291462684⟩, ⟨84849845147, 89756024868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 157941760 163512320 166461440 ⟨⟨89139174581, 89139174588⟩, ⟨86683506804, 91617884670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 157941760 158597120 163512320 166461440 ⟨⟨88763918284, 88763918290⟩, ⟨86316736265, 91234012084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 158597120 159252480 160563200 163512320 ⟨⟨86923340369, 86923340372⟩, ⟨84490141944, 89379353284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 159252480 159907840 160563200 163512320 ⟨⟨86556961041, 86556961049⟩, ⟨84132125971, 89004481608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 158597120 159252480 163512320 166461440 ⟨⟨88390437634, 88390437638⟩, ⟨85951685138, 90851972549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 159252480 159907840 163512320 166461440 ⟨⟨88018716120, 88018716128⟩, ⟨85588337501, 90471748959⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 159907840 154664960 166461440 t = true :=
  ⟨_, (join_sr (m := 160563200) (by decide) (join_su (m := 158597120) (by decide) (join_sr (m := 157614080) (by decide) (join_su (m := 157941760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 157941760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 157614080) (by decide) (join_su (m := 159252480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 159252480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 158597120) (by decide) (join_sr (m := 163512320) (by decide) (join_su (m := 157941760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 157941760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163512320) (by decide) (join_su (m := 159252480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 159252480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (61/320 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
