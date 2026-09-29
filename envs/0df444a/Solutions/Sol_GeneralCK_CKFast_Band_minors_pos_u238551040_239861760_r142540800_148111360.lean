-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u238551040_239861760_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:47:23.552977+00:00
-- url     : https://prove2.me/submissions/92c3eb24-17b2-4741-8650-8b9c89d9b7cf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [91/320, 183/640]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 238551040 238878720 142540800 143933440 ⟨⟨45710003506, 45710003511⟩, ⟨44884810450, 46538255710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 238878720 239206400 142540800 143933440 ⟨⟨45604985242, 45604985247⟩, ⟨44780821919, 46432201532⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 238551040 238878720 143933440 145326080 ⟨⟨46143267512, 46143267517⟩, ⟨45317122960, 46972472560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 238878720 239206400 143933440 145326080 ⟨⟨46037301734, 46037301739⟩, ⟨45212188386, 46865469400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 239206400 239534080 142540800 143933440 ⟨⟨45500113742, 45500113748⟩, ⟨44676977826, 46326296460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239534080 239861760 142540800 143933440 ⟨⟨45395388450, 45395388457⟩, ⟨44573277628, 46220539931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 239206400 239534080 143933440 145326080 ⟨⟨45931483739, 45931483744⟩, ⟨45107399270, 46758616367⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239534080 239861760 143933440 145326080 ⟨⟨45825812968, 45825812973⟩, ⟨45002755063, 46651912896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 238878720 145326080 146718720 ⟨⟨46576333889, 46576333895⟩, ⟨45749238198, 47406491418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238878720 239206400 145326080 146718720 ⟨⟨46469421870, 46469421875⟩, ⟨45643358850, 47298540555⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 238878720 146718720 148111360 ⟨⟨47009203102, 47009203107⟩, ⟨46181156628, 47840312753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 238878720 239206400 146718720 148111360 ⟨⟨46901346109, 46901346116⟩, ⟨46074333771, 47731415461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 239206400 239534080 145326080 146718720 ⟨⟨46362658645, 46362658650⟩, ⟨45537625971, 47190740834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239534080 239861760 145326080 146718720 ⟨⟨46256043654, 46256043659⟩, ⟨45432039007, 47083091684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239206400 239534080 146718720 148111360 ⟨⟨46793638918, 46793638924⟩, ⟨45967658386, 47622670318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239534080 239861760 146718720 148111360 ⟨⟨46686080964, 46686080969⟩, ⟨45861129918, 47514076750⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 238551040 239861760 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 239206400) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 238878720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239534080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 239206400) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 238878720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 238878720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 239534080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239534080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (91/320 : ℝ) (183/640 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((238551040 : ℤ) : ℝ) / (D : ℝ)) = (91/320 : ℝ) := by norm_num [D]
  have e1 : (((239861760 : ℤ) : ℝ) / (D : ℝ)) = (183/640 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
