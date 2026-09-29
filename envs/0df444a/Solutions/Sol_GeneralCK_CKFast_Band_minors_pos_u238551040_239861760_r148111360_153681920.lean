-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_239861760_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:10:09.830805+00:00
-- url     : https://prove2.me/submissions/30f0431e-b92a-4494-9d49-19160c208bcc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 183/640]`, `ρ ∈ [113/640, 469/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 238878720 148111360 149504000 ⟨⟨47441875615, 47441875620⟩, ⟨46612878715, 48273937030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238878720 239206400 148111360 149504000 ⟨⟨47333074915, 47333074922⟩, ⟨46505113607, 48164094579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 238878720 149504000 150896640 ⟨⟨47874351890, 47874351896⟩, ⟨47044404917, 48707364711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 238878720 239206400 149504000 150896640 ⟨⟨47764608746, 47764608752⟩, ⟨46935698819, 48596578368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239206400 239534080 148111360 149504000 ⟨⟨47224425016, 47224425022⟩, ⟨46397496970, 48054405277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239534080 239861760 148111360 149504000 ⟨⟨47115925349, 47115925354⟩, ⟨46290028244, 47944868550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239534080 149504000 150896640 ⟨⟨47655017394, 47655017400⟩, ⟨46827142178, 48485946170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239534080 239861760 149504000 150896640 ⟨⟨47545577264, 47545577269⟩, ⟨46718734437, 48375467535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 238878720 150896640 152289280 ⟨⟨48306632392, 48306632397⟩, ⟨47475735700, 49140596260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238878720 239206400 150896640 152289280 ⟨⟨48195948060, 48195948065⟩, ⟨47366089860, 49028867290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 238878720 152289280 153681920 ⟨⟨48738717579, 48738717585⟩, ⟨47906871522, 49573632140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 238878720 239206400 152289280 153681920 ⟨⟨48627093315, 48627093320⟩, ⟨47796287190, 49460961801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239206400 239534080 150896640 152289280 ⟨⟨48085416507, 48085416512⟩, ⟨47256594465, 48917293450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239534080 239861760 150896640 152289280 ⟨⟨47975037157, 47975037162⟩, ⟨47147248949, 48805874157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239206400 239534080 152289280 153681920 ⟨⟨48515622807, 48515622813⟩, ⟨47685854282, 49348447572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239534080 239861760 152289280 153681920 ⟨⟨48404305480, 48404305485⟩, ⟨47575572228, 49236088870⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 239861760 148111360 153681920 t = true :=
  ⟨_, (join_sr (m := 150896640) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 149504000) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 238878720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 149504000) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239534080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239206400) (by decide) (join_sr (m := 152289280) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 238878720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 152289280) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239534080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (183/640 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
