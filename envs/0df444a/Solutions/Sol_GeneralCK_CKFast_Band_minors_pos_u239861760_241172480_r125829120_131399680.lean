-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u239861760_241172480_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:36:58.701744+00:00
-- url     : https://prove2.me/submissions/6d19135f-73e7-4df8-9a35-54b94b9383b1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [183/640, 23/80]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 239861760 240189440 125829120 127221760 ⟨⟨40121861967, 40121861969⟩, ⟨39312147919, 40934593848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 240189440 240517120 125829120 127221760 ⟨⟨40028847475, 40028847480⟩, ⟨39220135930, 40840570685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239861760 240189440 127221760 128614400 ⟨⟨40553688414, 40553688416⟩, ⟨39743024638, 41367371432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 240189440 240517120 127221760 128614400 ⟨⟨40459715221, 40459715226⟩, ⟨39650055476, 41272388046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 240517120 240844800 125829120 127221760 ⟨⟨39935964943, 39935964949⟩, ⟨39128253640, 40746681764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240844800 241172480 125829120 127221760 ⟨⟨39843213870, 39843213876⟩, ⟨39036500551, 40652926579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 240517120 240844800 127221760 128614400 ⟨⟨40365875077, 40365875082⟩, ⟨39557217099, 41177539993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240844800 241172480 127221760 128614400 ⟨⟨40272167475, 40272167480⟩, ⟨39464509004, 41082826760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240189440 128614400 130007040 ⟨⟨40985316806, 40985316809⟩, ⟨40173703650, 41799950612⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 240189440 240517120 128614400 130007040 ⟨⟨40890386203, 40890386208⟩, ⟨40079778601, 41704008298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 240189440 130007040 131399680 ⟨⟨41416747606, 41416747608⟩, ⟨40604185417, 42232331847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240189440 240517120 130007040 131399680 ⟨⟨41320860880, 41320860886⟩, ⟨40509305761, 42135431900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 240517120 240844800 128614400 130007040 ⟨⟨40795589730, 40795589736⟩, ⟨39985985416, 41608202402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240844800 241172480 128614400 130007040 ⟨⟨40700926877, 40700926882⟩, ⟨39892323586, 41512532404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 240844800 130007040 131399680 ⟨⟨41225109359, 41225109364⟩, ⟨40414559042, 42038669445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240844800 241172480 130007040 131399680 ⟨⟨41129492527, 41129492532⟩, ⟨40319944747, 41942043962⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 239861760 241172480 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 240189440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240844800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 240517120) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 240189440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240844800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (183/640 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
