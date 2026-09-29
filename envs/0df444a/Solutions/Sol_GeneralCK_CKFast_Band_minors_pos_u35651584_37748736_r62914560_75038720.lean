-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u35651584_37748736_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:35:16.972731+00:00
-- url     : https://prove2.me/submissions/9dec6dde-7ed2-423b-a18c-06d590e7f36f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/400, 9/200]`, `ρ ∈ [3/40, 229/2560]` by 13 cells of the computing
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
theorem cell0 : cellOK 35651584 36175872 62914560 65945600 ⟨⟨117834415878, 117834415894⟩, ⟨111250284495, 124593862718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 36175872 36700160 62914560 65945600 ⟨⟨116818758607, 116818758627⟩, ⟨110303358353, 123506210745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 35651584 36175872 65945600 68976640 ⟨⟨122197607890, 122197607909⟩, ⟨115617524371, 128949559963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 36175872 36700160 65945600 68976640 ⟨⟨121158368698, 121158368713⟩, ⟨114646351376, 127839102431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 36700160 37224448 62914560 65945600 ⟨⟨115821097989, 115821098004⟩, ⟨109372939728, 122438138353⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 37224448 37748736 62914560 65945600 ⟨⟨114840928611, 114840928629⟩, ⟨108458571327, 121389088418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 36700160 37224448 65945600 68976640 ⟨⟨120137281462, 120137281482⟩, ⟨113691872487, 126748343958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 37224448 37748736 65945600 68976640 ⟨⟨119133843029, 119133843044⟩, ⟨112753631090, 125676731446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 35651584 36700160 68976640 72007680 ⟨⟨125952285818, 125952285837⟩, ⟨116554140186, 135704566668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 35651584 36700160 72007680 75038720 ⟨⟨130156781946, 130156781961⟩, ⟨120761785838, 139899483070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 36700160 37224448 68976640 72007680 ⟨⟨124380499215, 124380499235⟩, ⟨117938895849, 130984605075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 37224448 37748736 68976640 72007680 ⟨⟨123354971927, 123354971942⟩, ⟨116977949380, 129891618717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 36700160 37748736 72007680 75038720 ⟨⟨128027869827, 128027869842⟩, ⟨118816570675, 137574910945⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 35651584 37748736 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 36700160) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 36175872) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 36175872) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 37224448) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 37224448) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 36700160) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 72007680) (by decide) (join_su (m := 37224448) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/400 : ℝ) (9/200 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((35651584 : ℤ) : ℝ) / (D : ℝ)) = (17/400 : ℝ) := by norm_num [D]
  have e1 : (((37748736 : ℤ) : ℝ) / (D : ℝ)) = (9/200 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
