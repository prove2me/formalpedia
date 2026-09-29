-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u175636480_178257920_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:42.660092+00:00
-- url     : https://prove2.me/submissions/5ee82d4a-6cab-4604-ab5c-772a1482002e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [67/320, 17/80]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 175636480 176291840 125829120 127221760 ⟨⟨61651916726, 61651916734⟩, ⟨59914435920, 63401970081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 175636480 176291840 127221760 128614400 ⟨⟨62297539786, 62297539794⟩, ⟨60557754416, 64049897658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 176291840 176947200 125829120 127221760 ⟨⟨61387698560, 61387698566⟩, ⟨59655056363, 63132852282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 176291840 176947200 127221760 128614400 ⟨⟨62030803841, 62030803847⟩, ⟨60295863306, 63778255976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 175636480 176291840 128614400 130007040 ⟨⟨62942519980, 62942519986⟩, ⟨61200433748, 64697178631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 175636480 176291840 130007040 131399680 ⟨⟨63586859493, 63586859501⟩, ⟨61842476088, 65343815205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 176291840 176947200 128614400 130007040 ⟨⟨62673273534, 62673273540⟩, ⟨60936038308, 64423020407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 176291840 176947200 130007040 131399680 ⟨⟨63315109795, 63315109803⟩, ⟨61575583504, 65067147745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 176947200 177602560 125829120 127221760 ⟨⟨61124655159, 61124655166⟩, ⟨59396820241, 62864941109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 176947200 177602560 127221760 128614400 ⟨⟨61765251069, 61765251075⟩, ⟨60035124036, 63507829332⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 177602560 178257920 125829120 127221760 ⟨⟨60862775921, 60862775927⟩, ⟨59139717258, 62598225644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 177602560 178257920 127221760 128614400 ⟨⟨61500870809, 61500870816⟩, ⟨59775526247, 63238606753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 176947200 177602560 128614400 130007040 ⟨⟨62405218594, 62405218601⟩, ⟨60672803030, 64150085556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 176947200 177602560 130007040 131399680 ⟨⟨63044559858, 63044559864⟩, ⟨61309859333, 64791711914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 177602560 178257920 128614400 130007040 ⟨⟨62138344439, 62138344445⟩, ⟨60410717502, 63878363045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 177602560 178257920 130007040 131399680 ⟨⟨62775198900, 62775198908⟩, ⟨61045293102, 64517496622⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 175636480 178257920 125829120 131399680 t = true :=
  ⟨_, (join_su (m := 176947200) (by decide) (join_sr (m := 128614400) (by decide) (join_su (m := 176291840) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 127221760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 176291840) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 130007040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 128614400) (by decide) (join_su (m := 177602560) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 127221760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 177602560) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 130007040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (67/320 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((175636480 : ℤ) : ℝ) / (D : ℝ)) = (67/320 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
