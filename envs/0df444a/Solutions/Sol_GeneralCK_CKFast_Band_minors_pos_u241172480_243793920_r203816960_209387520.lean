-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_243793920_r203816960_209387520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:21:03.81355+00:00
-- url     : https://prove2.me/submissions/cdc75f0f-99ab-469c-babf-2864d3f32d61

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 93/320]`, `ρ ∈ [311/1280, 639/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241827840 203816960 205209600 ⟨⟨63361362145, 63361362150⟩, ⟨61893507019, 64837892665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 241827840 205209600 206602240 ⟨⟨63778774836, 63778774842⟩, ⟨62309201895, 65257028621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241827840 242483200 203816960 205209600 ⟨⟨63073548647, 63073548652⟩, ⟨61608710748, 64547034908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241827840 242483200 205209600 206602240 ⟨⟨63489184806, 63489184811⟩, ⟨62022633278, 64964390176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 241827840 206602240 207994880 ⟨⟨64196018804, 64196018811⟩, ⟨62724728370, 65675995520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 241827840 207994880 209387520 ⟨⟨64613094448, 64613094453⟩, ⟨63140086845, 66094793759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242483200 206602240 207994880 ⟨⟨63904654377, 63904654382⟩, ⟨62436389529, 65381578534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 241827840 242483200 207994880 209387520 ⟨⟨64319957751, 64319957757⟩, ⟨62849979894, 65798600377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 243138560 203816960 205209600 ⟨⟨62786452485, 62786452492⟩, ⟨61324617967, 64256908498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242483200 243138560 205209600 206602240 ⟨⟨63200315026, 63200315032⟩, ⟨61736771062, 64672485994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243138560 243793920 203816960 205209600 ⟨⟨62500068509, 62500068514⟩, ⟨61041223619, 63967508188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 243138560 243793920 205209600 206602240 ⟨⟨62912160330, 62912160336⟩, ⟨61451610178, 64381310811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 242483200 243138560 206602240 207994880 ⟨⟨63614013092, 63614013099⟩, ⟨62148759981, 65087898707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242483200 243138560 207994880 209387520 ⟨⟨64027547071, 64027547077⟩, ⟨62560585106, 65503147027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243793920 206602240 207994880 ⟨⟨63324089770, 63324089777⟩, ⟨61861834639, 64794950759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243138560 243793920 207994880 209387520 ⟨⟨63735857209, 63735857214⟩, ⟨62271897381, 65208428413⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 243793920 203816960 209387520 t = true :=
  ⟨_, (join_su (m := 242483200) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 205209600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 241827840) (by decide) (join_sr (m := 207994880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 207994880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 206602240) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 205209600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 243138560) (by decide) (join_sr (m := 207994880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 207994880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (639/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((209387520 : ℤ) : ℝ) / (D : ℝ)) = (639/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
