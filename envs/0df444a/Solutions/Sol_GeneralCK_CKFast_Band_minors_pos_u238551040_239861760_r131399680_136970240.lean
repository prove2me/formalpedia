-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_239861760_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:38:14.721973+00:00
-- url     : https://prove2.me/submissions/5518ea88-f112-4cf2-bc78-fc4cc206a195

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 183/640]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 238878720 131399680 132792320 ⟨⟨42236720656, 42236720663⟩, ⟨41419152550, 43057337014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238878720 239206400 131399680 132792320 ⟨⟨42139328791, 42139328798⟩, ⟨41322778446, 42958921159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 238878720 132792320 134184960 ⟨⟨42671582561, 42671582566⟩, ⟨41853060065, 43493154682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 238878720 239206400 132792320 134184960 ⟨⟨42573232861, 42573232866⟩, ⟨41755729641, 43393779482⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239206400 239534080 131399680 132792320 ⟨⟨42042075290, 42042075296⟩, ⟨41226540397, 42860645995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239534080 239861760 131399680 132792320 ⟨⟨41944959624, 41944959630⟩, ⟨41130437884, 42762510989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239534080 132792320 134184960 ⟨⟨42475022598, 42475022604⟩, ⟨41658536344, 43294546051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239534080 239861760 132792320 134184960 ⟨⟨42376951243, 42376951248⟩, ⟨41561479651, 43195453848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 238878720 134184960 135577600 ⟨⟨43106243079, 43106243085⟩, ⟨42286766560, 43928770596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238878720 239206400 134184960 135577600 ⟨⟨43006936848, 43006936853⟩, ⟨42188481113, 43828437361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 238878720 135577600 136970240 ⟨⟨43540702685, 43540702690⟩, ⟨42720272505, 44364185228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 238878720 239206400 135577600 136970240 ⟨⟨43440441222, 43440441227⟩, ⟨42621033331, 44262895263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239206400 239534080 134184960 135577600 ⟨⟨42907771121, 42907771126⟩, ⟨42090333858, 43728246962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239534080 239861760 134184960 135577600 ⟨⟨42808745364, 42808745370⟩, ⟨41992324270, 43628198859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239206400 239534080 135577600 136970240 ⟨⟨43340321323, 43340321328⟩, ⟨42521933406, 44161749198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239534080 239861760 135577600 136970240 ⟨⟨43240342451, 43240342456⟩, ⟨42422972204, 44060746485⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 239861760 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 238878720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239534080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239206400) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 238878720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239534080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (183/640 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
