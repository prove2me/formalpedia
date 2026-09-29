-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u239861760_241172480_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:47:03.313308+00:00
-- url     : https://prove2.me/submissions/c80af5c9-347b-4875-a120-6afe8556caa0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [183/640, 23/80]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 239861760 240189440 136970240 138362880 ⟨⟨43570953800, 43570953803⟩, ⟨42753651615, 44391285004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 240189440 240517120 136970240 138362880 ⟨⟨43470305637, 43470305642⟩, ⟨42654018031, 44289616139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 239861760 240189440 138362880 139755520 ⟨⟨44001208683, 44001208685⟩, ⟨43182959526, 44822488242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 240189440 240517120 138362880 139755520 ⟨⟨43899612041, 43899612046⟩, ⟨43082378949, 44719869417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 240517120 240844800 136970240 138362880 ⟨⟨43369797944, 43369797949⟩, ⟨42554522638, 44188090040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 240844800 241172480 136970240 138362880 ⟨⟨43269430189, 43269430196⟩, ⟨42455164911, 44086706174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 240517120 240844800 138362880 139755520 ⟨⟨43798156903, 43798156908⟩, ⟨42981937596, 44617394395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 240844800 241172480 138362880 139755520 ⟨⟨43696842732, 43696842737⟩, ⟨42881634935, 44515062634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 239861760 240189440 139755520 141148160 ⟨⟨44431269177, 44431269180⟩, ⟨43612073390, 45253496748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 240189440 240517120 139755520 141148160 ⟨⟨44328725318, 44328725323⟩, ⟨43510547076, 45149929230⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 240189440 141148160 142540800 ⟨⟨44861135738, 44861135741⟩, ⟨44040993659, 45684310976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 240189440 240517120 141148160 142540800 ⟨⟨44757645917, 44757645924⟩, ⟨43938522862, 45579796027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 240517120 240844800 139755520 141148160 ⟨⟨44226323988, 44226323993⟩, ⟨43409161011, 45046506541⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 240844800 241172480 139755520 141148160 ⟨⟨44124064649, 44124064654⟩, ⟨43307914659, 44943228140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 240844800 141148160 142540800 ⟨⟨44654299646, 44654299653⟩, ⟨43836193329, 45475426929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 240844800 241172480 141148160 142540800 ⟨⟨44551096383, 44551096388⟩, ⟨43734004525, 45371203135⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 239861760 241172480 136970240 142540800 t = true :=
  ⟨_, (join_sr (m := 139755520) (by decide) (join_su (m := 240517120) (by decide) (join_sr (m := 138362880) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 240189440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 138362880) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 240844800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 240517120) (by decide) (join_sr (m := 141148160) (by decide) (join_su (m := 240189440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 240189440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 141148160) (by decide) (join_su (m := 240844800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 240844800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (183/640 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
