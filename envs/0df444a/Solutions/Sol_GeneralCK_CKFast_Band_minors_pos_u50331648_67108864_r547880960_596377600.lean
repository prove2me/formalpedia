-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_67108864_r547880960_596377600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:21:27.406872+00:00
-- url     : https://prove2.me/submissions/fb84bb9e-9ffa-4eff-ab1c-3f666e8a4d4b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 2/25]`, `ρ ∈ [209/320, 91/128]` by 15 cells of the computing
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
theorem cell0 : cellOK 50331648 54525952 547880960 560005120 ⟨⟨439922565050, 439922565058⟩, ⟨413898195479, 466561206649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 54525952 560005120 572129280 ⟨⟨445921547369, 445921547373⟩, ⟨419961177347, 472467111045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 54525952 58720256 547880960 560005120 ⟨⟨430451817285, 430451817301⟩, ⟨404973932021, 456552257993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 54525952 58720256 560005120 572129280 ⟨⟨436445583763, 436445583779⟩, ⟨411018198642, 462467965877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 54525952 572129280 596377600 ⟨⟨454830968216, 454830968223⟩, ⟨421237765673, 489311577700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 54525952 58720256 572129280 584253440 ⟨⟨442391996504, 442391996519⟩, ⟨417014150498, 468337938755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 54525952 58720256 584253440 596377600 ⟨⟨448293366135, 448293366150⟩, ⟨422964085986, 474164463657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 58720256 62914560 547880960 560005120 ⟨⟨421278026005, 421278026019⟩, ⟨396322985211, 446861677047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 58720256 62914560 560005120 572129280 ⟨⟨427260708805, 427260708820⟩, ⟨402343686943, 452780245148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 62914560 67108864 547880960 560005120 ⟨⟨412379611267, 412379611282⟩, ⟨387925941471, 437466105176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 62914560 67108864 560005120 572129280 ⟨⟨418345862792, 418345862807⟩, ⟨393918664196, 443381195478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 58720256 62914560 572129280 584253440 ⟨⟨433196719093, 433196719107⟩, ⟨408317064415, 458653374524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 58720256 62914560 584253440 596377600 ⟨⟨439088292349, 439088292364⟩, ⟨414245329481, 464483293373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 62914560 67108864 572129280 584253440 ⟨⟨424266241039, 424266241054⟩, ⟨399865129273, 449251309806⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 62914560 67108864 584253440 596377600 ⟨⟨430142903448, 430142903463⟩, ⟨405767461453, 455078611670⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 67108864 547880960 596377600 t = true :=
  ⟨_, (join_su (m := 58720256) (by decide) (join_sr (m := 572129280) (by decide) (join_su (m := 54525952) (by decide) (join_sr (m := 560005120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 560005120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 54525952) (by decide) (leaf_ok cell4) (join_sr (m := 584253440) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 572129280) (by decide) (join_su (m := 62914560) (by decide) (join_sr (m := 560005120) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 560005120) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 62914560) (by decide) (join_sr (m := 584253440) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 584253440) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (209/320 : ℝ) (91/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((547880960 : ℤ) : ℝ) / (D : ℝ)) = (209/320 : ℝ) := by norm_num [D]
  have e3 : (((596377600 : ℤ) : ℝ) / (D : ℝ)) = (91/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
