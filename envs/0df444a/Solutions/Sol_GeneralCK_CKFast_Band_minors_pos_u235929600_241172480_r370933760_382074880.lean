-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r370933760_382074880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:55:46.473405+00:00
-- url     : https://prove2.me/submissions/f97293a4-f6fc-4ffb-9b45-db220f9e430a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [283/640, 583/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 370933760 373719040 ⟨⟨116243529682, 116243529688⟩, ⟨112855085200, 119669684314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 237240320 373719040 376504320 ⟨⟨117066335152, 117066335160⟩, ⟨113671078695, 120499332073⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 238551040 370933760 373719040 ⟨⟨115253801168, 115253801174⟩, ⟨111879410235, 118665718063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 373719040 376504320 ⟨⟨116070347916, 116070347922⟩, ⟨112689166272, 119489086664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 237240320 376504320 379289600 ⟨⟨117888592920, 117888592928⟩, ⟨114486526842, 121328429579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 237240320 379289600 382074880 ⟨⟨118710305837, 118710305844⟩, ⟨115301432475, 122156979700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 238551040 376504320 379289600 ⟨⟨116886359644, 116886359651⟩, ⟨113498389470, 120311917875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237240320 238551040 379289600 382074880 ⟨⟨117701839127, 117701839133⟩, ⟨114307082583, 121134214485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239861760 370933760 373719040 ⟨⟨114267975653, 114267975655⟩, ⟨110907530756, 117665764004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238551040 239861760 373719040 376504320 ⟨⟨115078270505, 115078270510⟩, ⟨111711056423, 118482859994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 241172480 370933760 373719040 ⟨⟨113286003097, 113286003103⟩, ⟨109939398032, 116669770775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 241172480 373719040 376504320 ⟨⟨114090052881, 114090052889⟩, ⟨110736700411, 117480600708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 376504320 379289600 ⟨⟨115888042803, 115888042807⟩, ⟨112514061543, 119299431235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238551040 239861760 379289600 382074880 ⟨⟨116697295242, 116697295246⟩, ⟨113316548795, 120115480439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 241172480 376504320 379289600 ⟨⟨114893592360, 114893592367⟩, ⟨111533494322, 118290918315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 379289600 382074880 ⟨⟨115696624154, 115696624160⟩, ⟨112329782371, 119100726231⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 370933760 382074880 t = true :=
  ⟨_, (join_su (m := 238551040) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 373719040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 373719040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 237240320) (by decide) (join_sr (m := 379289600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 379289600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 376504320) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 373719040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 373719040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 239861760) (by decide) (join_sr (m := 379289600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 379289600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (583/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((382074880 : ℤ) : ℝ) / (D : ℝ)) = (583/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
