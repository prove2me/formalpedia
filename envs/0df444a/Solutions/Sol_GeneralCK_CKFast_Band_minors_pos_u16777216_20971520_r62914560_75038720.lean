-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_20971520_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:17:10.617075+00:00
-- url     : https://prove2.me/submissions/5dd6ddba-7eaf-403f-ab4b-087d720d4452

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 1/40]`, `ρ ∈ [3/40, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 17825792 62914560 65945600 ⟨⟨172086223226, 172086223257⟩, ⟨156910456292, 188113825389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 16777216 17825792 65945600 68976640 ⟨⟨177313023219, 177313023243⟩, ⟨162231573105, 193217104235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 17825792 18874368 62914560 65945600 ⟨⟨167609441499, 167609441529⟩, ⟨152948729451, 183073269936⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 17825792 18874368 65945600 68976640 ⟨⟨172794559927, 172794559950⟩, ⟨158216347089, 188149466494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 16777216 17825792 68976640 72007680 ⟨⟨182398908879, 182398908910⟩, ⟨167412429156, 198180214481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 16777216 17825792 72007680 75038720 ⟨⟨187351652716, 187351652741⟩, ⟨172460509445, 203011131766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 17825792 18874368 68976640 72007680 ⟨⟨177843755044, 177843755074⟩, ⟨163348999712, 193089991488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 17825792 18874368 72007680 75038720 ⟨⟨182764315144, 182764315168⟩, ⟨168353692432, 197902347195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 18874368 19922944 62914560 65945600 ⟨⟨163380025323, 163380025352⟩, ⟨149198910044, 178319749775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 18874368 19922944 65945600 68976640 ⟨⟨168520869823, 168520869846⟩, ⟨154411838256, 183364535467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 19922944 20971520 62914560 65945600 ⟨⟨159376719544, 159376719571⟩, ⟨145643300644, 173827976928⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 19922944 20971520 65945600 68976640 ⟨⟨164471274024, 164471274047⟩, ⟨150800732794, 178837840355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 18874368 19922944 68976640 72007680 ⟨⟨173530633780, 173530633809⟩, ⟨159494881219, 188278095453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 18874368 19922944 72007680 75038720 ⟨⟨178416154191, 178416154213⟩, ⟨164454599879, 193067485839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 19922944 20971520 68976640 72007680 ⟨⟨169439431337, 169439431359⟩, ⟨155833145384, 183720843425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 19922944 20971520 72007680 75038720 ⟨⟨174287608280, 174287608302⟩, ⟨160746688201, 188483622961⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 20971520 62914560 75038720 t = true :=
  ⟨_, (join_su (m := 18874368) (by decide) (join_sr (m := 68976640) (by decide) (join_su (m := 17825792) (by decide) (join_sr (m := 65945600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 65945600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 17825792) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 72007680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 68976640) (by decide) (join_su (m := 19922944) (by decide) (join_sr (m := 65945600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 65945600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 19922944) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 72007680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/40 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((20971520 : ℤ) : ℝ) / (D : ℝ)) = (1/40 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
