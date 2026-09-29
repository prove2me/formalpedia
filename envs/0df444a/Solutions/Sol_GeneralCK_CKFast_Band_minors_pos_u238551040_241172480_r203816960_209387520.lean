-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_241172480_r203816960_209387520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:56:27.223819+00:00
-- url     : https://prove2.me/submissions/073f36a7-4ae0-4643-8db6-b7c885a86eac

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 23/80]`, `ρ ∈ [311/1280, 639/2560]` by 13 cells of the computing
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
theorem cell0 : cellOK 238551040 239206400 203816960 205209600 ⟨⟨64519893948, 64519893954⟩, ⟨63039829485, 66008743614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238551040 239206400 205209600 206602240 ⟨⟨64944442240, 64944442246⟩, ⟨63462643199, 66435031807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239206400 239861760 203816960 205209600 ⟨⟨64229158779, 64229158785⟩, ⟨62752167913, 65714907142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 239206400 239861760 205209600 206602240 ⟨⟨64651918718, 64651918725⟩, ⟨63173197467, 66139402821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239206400 206602240 209387520 ⟨⟨65580932027, 65580932032⟩, ⟨63846986042, 67327338639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239206400 239861760 206602240 209387520 ⟨⟨65285730144, 65285730149⟩, ⟨63556134859, 67027739137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239861760 240517120 203816960 205209600 ⟨⟨63939161958, 63939161964⟩, ⟨62465230447, 65421823430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239861760 240517120 205209600 206602240 ⟨⟨64360136524, 64360136531⟩, ⟨62884478819, 65844529576⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 240517120 241172480 203816960 205209600 ⟨⟨63649898173, 63649898176⟩, ⟨62179011874, 65129487063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 240517120 241172480 205209600 206602240 ⟨⟨64069090328, 64069090330⟩, ⟨62596482025, 65550406639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 240517120 206602240 209387520 ⟨⟨64991274015, 64991274020⟩, ⟨63266010684, 66728904418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240517120 241172480 206602240 207994880 ⟨⟨64488111603, 64488111606⟩, ⟨63013781633, 65971154987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 240517120 241172480 207994880 209387520 ⟨⟨64906962402, 64906962403⟩, ⟨63430911102, 66391732512⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 241172480 203816960 209387520 t = true :=
  ⟨_, (join_su (m := 239861760) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 205209600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 239206400) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 206602240) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 205209600) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 240517120) (by decide) (leaf_ok cell10) (join_sr (m := 207994880) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (639/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((209387520 : ℤ) : ℝ) / (D : ℝ)) = (639/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
