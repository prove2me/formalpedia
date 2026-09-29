-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u242483200_243793920_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:20:08.750979+00:00
-- url     : https://prove2.me/submissions/0d564cb8-1401-45f1-8033-98ce65b09a71

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/128, 93/320]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 242483200 242810880 125829120 127221760 ⟨⟨39381412886, 39381412891⟩, ⟨38579655941, 40186138880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 242810880 243138560 125829120 127221760 ⟨⟨39289440101, 39289440106⟩, ⟨38488667777, 40093175463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 242810880 127221760 128614400 ⟨⟨39805599982, 39805599988⟩, ⟨39002905469, 40611264995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242810880 243138560 127221760 128614400 ⟨⟨39712677097, 39712677103⟩, ⟨38910968718, 40517349974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243138560 243466240 125829120 127221760 ⟨⟨39197595307, 39197595311⟩, ⟨38397805412, 40000342253⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243466240 243793920 125829120 127221760 ⟨⟨39105878017, 39105878022⟩, ⟨38307068358, 39907638759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 243138560 243466240 127221760 128614400 ⟨⟨39619883264, 39619883267⟩, ⟨38819158820, 40423566220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 243466240 243793920 127221760 128614400 ⟨⟨39527217988, 39527217994⟩, ⟨38727475289, 40329913240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 242483200 242810880 128614400 130007040 ⟨⟨40229599159, 40229599164⟩, ⟨39425967387, 41036202881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 242810880 243138560 128614400 130007040 ⟨⟨40135727411, 40135727416⟩, ⟨39333083277, 40941337495⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 242483200 242810880 130007040 131399680 ⟨⟨40653410848, 40653410853⟩, ⟨39848842121, 41460952969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 242810880 243138560 130007040 131399680 ⟨⟨40558591470, 40558591475⟩, ⟨39755011882, 41365138458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243138560 243466240 128614400 130007040 ⟨⟨40041985766, 40041985770⟩, ⟨39240327072, 40846604433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243466240 243793920 128614400 130007040 ⟨⟨39948373730, 39948373735⟩, ⟨39147698279, 40752003194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 243138560 243466240 130007040 131399680 ⟨⟨40463903240, 40463903244⟩, ⟨39661310591, 41269457316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 243466240 243793920 130007040 131399680 ⟨⟨40369345661, 40369345666⟩, ⟨39567737754, 41173909044⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 242483200 243793920 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 243138560) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 242810880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 243466240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 243138560) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 242810880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 242810880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 243466240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 243466240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/128 : ℝ) (93/320 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e1 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
