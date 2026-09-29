-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u112721920_115343360_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:11:48.330694+00:00
-- url     : https://prove2.me/submissions/c9c00793-6ba7-4608-8db1-ab716fc3390d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/320, 11/80]`, `ρ ∈ [91/640, 5/32]` by 15 cells of the computing
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
theorem cell0 : cellOK 112721920 113377280 119275520 122224640 ⟨⟨90852589149, 90852589153⟩, ⟨87740485940, 94002555416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 113377280 114032640 119275520 122224640 ⟨⟨90412281428, 90412281436⟩, ⟨87314531924, 93547590297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 112721920 113377280 122224640 125173760 ⟨⟨92852205846, 92852205848⟩, ⟨89733191961, 96008939204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 113377280 114032640 122224640 125173760 ⟨⟨92403940245, 92403940253⟩, ⟨89299284114, 95546015123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 114032640 114688000 119275520 122224640 ⟨⟨89975157567, 89975157575⟩, ⟨86891627124, 93095947520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 114688000 115343360 119275520 122224640 ⟨⟨89541177185, 89541177195⟩, ⟨86471733099, 92647584705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 114032640 114688000 122224640 125173760 ⟨⟨91958895622, 91958895629⟩, ⟨88868463092, 95086449953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 114688000 115343360 122224640 125173760 ⟨⟨91517031336, 91517031343⟩, ⟨88440690178, 94630201064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 112721920 113377280 125173760 128122880 ⟨⟨94843117782, 94843117786⟩, ⟨91717286164, 98006525408⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 113377280 114032640 125173760 128122880 ⟨⟨94386995172, 94386995180⟩, ⟨91275524084, 97535744495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 112721920 114032640 128122880 131072000 ⟨⟨96593072049, 96593072057⟩, ⟨91705396289, 101572511519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 114032640 114688000 125173760 128122880 ⟨⟨93934129392, 93934129401⟩, ⟨90836885187, 97068357778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 114688000 115343360 125173760 128122880 ⟨⟨93484479561, 93484479568⟩, ⟨90401330499, 96604322403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 114032640 114688000 128122880 131072000 ⟨⟨95900956791, 95900956799⟩, ⟨92796989685, 99041770549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 114688000 115343360 128122880 131072000 ⟨⟨95443618091, 95443618101⟩, ⟨92353748696, 98570046560⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 112721920 115343360 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 114032640) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 113377280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 113377280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 114688000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 114688000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 114032640) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 113377280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 128122880) (by decide) (join_su (m := 114688000) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 114688000) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/320 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
