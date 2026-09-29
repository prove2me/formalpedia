-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r203816960_209387520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:23:48.120587+00:00
-- url     : https://prove2.me/submissions/c9ad4e4f-6d4d-407a-a71f-a5055a4bb121

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [311/1280, 639/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 203816960 205209600 ⟨⟨61078653788, 61078653793⟩, ⟨59634554091, 62531217164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247070720 205209600 206602240 ⟨⟨61481934945, 61481934952⟩, ⟨60036150867, 62936188383⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247070720 247726080 203816960 205209600 ⟨⟨60796436893, 60796436897⟩, ⟨59355246293, 62246065422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247070720 247726080 205209600 206602240 ⟨⟨61197964396, 61197964400⟩, ⟨59755093582, 62649278844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247070720 206602240 207994880 ⟨⟨61885063873, 61885063878⟩, ⟨60437595631, 63341007143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247070720 207994880 209387520 ⟨⟨62288040918, 62288040923⟩, ⟨60838888734, 63745673793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247070720 247726080 206602240 207994880 ⟨⟨61599341635, 61599341639⟩, ⟨60154790816, 63052341786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247070720 247726080 207994880 209387520 ⟨⟨62000568957, 62000568959⟩, ⟨60554338340, 63455254594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 247726080 248381440 203816960 205209600 ⟨⟨60514897193, 60514897200⟩, ⟨59076602591, 61961604132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247726080 248381440 205209600 206602240 ⟨⟨60914673830, 60914673836⟩, ⟨59474703181, 62363062548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 248381440 249036800 203816960 205209600 ⟨⟨60234029843, 60234029848⟩, ⟨58798618225, 61677828355⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248381440 249036800 205209600 206602240 ⟨⟨60632058386, 60632058393⟩, ⟨59194974887, 62077534540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247726080 248381440 206602240 207994880 ⟨⟨61314302151, 61314302156⟩, ⟨59872655652, 62764372444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 247726080 248381440 207994880 209387520 ⟨⟨61713782497, 61713782503⟩, ⟨60270460342, 63165534161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248381440 249036800 206602240 207994880 ⟨⟨61029940543, 61029940550⟩, ⟨59591185345, 62477094147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248381440 249036800 207994880 209387520 ⟨⟨61427676649, 61427676654⟩, ⟨59987249936, 62876507509⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 203816960 209387520 t = true :=
  ⟨_, (join_su (m := 247726080) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 247070720) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 205209600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247070720) (by decide) (join_sr (m := 207994880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 207994880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 206602240) (by decide) (join_su (m := 248381440) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 205209600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 248381440) (by decide) (join_sr (m := 207994880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 207994880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (639/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((209387520 : ℤ) : ℝ) / (D : ℝ)) = (639/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
