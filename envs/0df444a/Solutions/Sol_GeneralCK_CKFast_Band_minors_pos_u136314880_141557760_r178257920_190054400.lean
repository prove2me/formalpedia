-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_141557760_r178257920_190054400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:34:16.947169+00:00
-- url     : https://prove2.me/submissions/a3d84bb8-c31e-4c7a-8ff4-48851f39e3e8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 27/160]`, `ρ ∈ [17/80, 29/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 137625600 178257920 181207040 ⟨⟨110179678141, 110179678150⟩, ⟨105750892124, 114678165831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 137625600 181207040 184156160 ⟨⟨111806253902, 111806253910⟩, ⟨107367410834, 116314667534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 137625600 138936320 178257920 181207040 ⟨⟨109242505218, 109242505227⟩, ⟨104844363907, 113709565289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 137625600 138936320 181207040 184156160 ⟨⟨110857850025, 110857850032⟩, ⟨106449663920, 115334829902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 137625600 184156160 187105280 ⟨⟨113428086458, 113428086468⟩, ⟨108979251110, 117946360695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 137625600 187105280 190054400 ⟨⟨115045219019, 115045219028⟩, ⟨110586455343, 119573289345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 137625600 138936320 184156160 187105280 ⟨⟨112468549774, 112468549783⟩, ⟨108050382038, 116955385715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 137625600 138936320 187105280 190054400 ⟨⟨114074646394, 114074646401⟩, ⟨109646559403, 118571275447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 138936320 140247040 178257920 181207040 ⟨⟨108315259230, 108315259239⟩, ⟨103947303030, 112751366297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 138936320 140247040 181207040 184156160 ⟨⟨109919436617, 109919436624⟩, ⟨105541449426, 114365455602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 140247040 141557760 178257920 181207040 ⟨⟨107397742670, 107397742676⟩, ⟨103059522311, 111803360625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 140247040 141557760 181207040 184156160 ⟨⟨108990815716, 108990815718⟩, ⟨104642579637, 113406336034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 138936320 140247040 184156160 187105280 ⟨⟨111519065114, 111519065121⟩, ⟨107131108517, 115974933840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 138936320 140247040 187105280 190054400 ⟨⟨113114185403, 113114185412⟩, ⟨108716320238, 117579842456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 140247040 141557760 184156160 187105280 ⟨⟨110579434096, 110579434101⟩, ⟨106221242344, 115004796140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140247040 141557760 187105280 190054400 ⟨⟨112163637297, 112163637303⟩, ⟨107795549191, 116598781153⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 141557760 178257920 190054400 t = true :=
  ⟨_, (join_su (m := 138936320) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 137625600) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 181207040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 137625600) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 187105280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184156160) (by decide) (join_su (m := 140247040) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 181207040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 140247040) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 187105280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (29/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
