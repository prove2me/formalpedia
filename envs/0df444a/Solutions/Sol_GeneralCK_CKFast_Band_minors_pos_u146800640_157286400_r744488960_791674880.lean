-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_157286400_r744488960_791674880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:14:21.847145+00:00
-- url     : https://prove2.me/submissions/b4521c22-b38d-45cd-9c6c-995f801210d0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 3/16]`, `ρ ∈ [71/80, 151/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 149422080 744488960 756285440 ⟨⟨352420997169, 352420997180⟩, ⟨339197833912, 365872467709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149422080 152043520 744488960 756285440 ⟨⟨348246690628, 348246690632⟩, ⟨335136987224, 361585260624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 149422080 756285440 768081920 ⟨⟨357003434902, 357003434913⟩, ⟨343734571072, 370496768378⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 149422080 152043520 756285440 768081920 ⟨⟨352795747236, 352795747242⟩, ⟨339639301388, 366177369794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152043520 154664960 744488960 756285440 ⟨⟨344100385779, 344100385789⟩, ⟨331103184215, 357326937343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154664960 157286400 744488960 756285440 ⟨⟨339981446902, 339981446913⟩, ⟨327095804497, 353096849704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 152043520 154664960 756285440 768081920 ⟨⟨348615605631, 348615605642⟩, ⟨335570669691, 361886346644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 154664960 157286400 756285440 768081920 ⟨⟨344462387488, 344462387499⟩, ⟨331528067458, 357623065154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 149422080 768081920 779878400 ⟨⟨361574180367, 361574180380⟩, ⟨348259839897, 375109131731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 149422080 152043520 768081920 779878400 ⟨⟨357333389299, 357333389305⟩, ⟨344130424064, 370757818953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 149422080 779878400 791674880 ⟨⟨366133753892, 366133753904⟩, ⟨352774147336, 379710090608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 149422080 152043520 779878400 791674880 ⟨⟨361860121699, 361860121705⟩, ⟨348610847081, 375327125235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 152043520 154664960 768081920 779878400 ⟨⟨353119687221, 353119687234⟩, ⟨340027238397, 366434372615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154664960 157286400 768081920 779878400 ⟨⟨348932464425, 348932464436⟩, ⟨335949686052, 362138173040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 152043520 154664960 779878400 791674880 ⟨⟨357613120265, 357613120276⟩, ⟨344473367325, 370971516937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 154664960 157286400 779878400 791674880 ⟨⟨353392152534, 353392152546⟩, ⟨340361122719, 366642659858⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 157286400 744488960 791674880 t = true :=
  ⟨_, (join_sr (m := 768081920) (by decide) (join_su (m := 152043520) (by decide) (join_sr (m := 756285440) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 149422080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 756285440) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 154664960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 152043520) (by decide) (join_sr (m := 779878400) (by decide) (join_su (m := 149422080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 149422080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 779878400) (by decide) (join_su (m := 154664960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 154664960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (71/80 : ℝ) (151/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  have e3 : (((791674880 : ℤ) : ℝ) / (D : ℝ)) = (151/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
