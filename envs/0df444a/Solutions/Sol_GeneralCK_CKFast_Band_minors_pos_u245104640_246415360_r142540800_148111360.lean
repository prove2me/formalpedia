-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u245104640_246415360_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:39:45.027345+00:00
-- url     : https://prove2.me/submissions/c224f144-1f63-4475-86ab-fe4e807c4c5e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [187/640, 47/160]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 245104640 245432320 142540800 143933440 ⟨⟨43636902743, 43636902748⟩, ⟨42831872794, 44444871918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 245432320 245760000 142540800 143933440 ⟨⟨43534717070, 43534717076⟩, ⟨42730672014, 44341695559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 245104640 245432320 143933440 145326080 ⟨⟨44051406436, 44051406441⟩, ⟨43245454125, 44860299428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 245432320 245760000 143933440 145326080 ⟨⟨43948293024, 43948293030⟩, ⟨43143327045, 44756193897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245760000 246087680 142540800 143933440 ⟨⟨43432667508, 43432667513⟩, ⟨42629605185, 44238657487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246087680 246415360 142540800 143933440 ⟨⟨43330753544, 43330753551⟩, ⟨42528671806, 44135757182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245760000 246087680 143933440 145326080 ⟨⟨43845316678, 43845316685⟩, ⟨43041334869, 44652227609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 246087680 246415360 143933440 145326080 ⟨⟨43742476885, 43742476892⟩, ⟨42939477096, 44548400044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245432320 145326080 146718720 ⟨⟨44465736715, 44465736720⟩, ⟨43658862302, 45275553261⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245432320 245760000 145326080 146718720 ⟨⟨44361696709, 44361696714⟩, ⟨43555810061, 45170519706⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 245432320 146718720 148111360 ⟨⟨44879893973, 44879893979⟩, ⟨44072097719, 45690633811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245432320 245760000 146718720 148111360 ⟨⟨44774928513, 44774928518⟩, ⟨43968121454, 45584673377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245760000 246087680 145326080 146718720 ⟨⟨44257794717, 44257794723⟩, ⟨43452893673, 45065626344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 246087680 246415360 145326080 146718720 ⟨⟨44154030225, 44154030230⟩, ⟨43350112632, 44960872653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246087680 146718720 148111360 ⟨⟨44670102011, 44670102017⟩, ⟨43864281984, 45478854081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 246087680 246415360 146718720 148111360 ⟨⟨44565413950, 44565413955⟩, ⟨43760578799, 45373175399⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 245104640 246415360 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 245432320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 245432320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 246087680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 246087680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 245760000) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 245432320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 245432320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 146718720) (by decide) (join_su (m := 246087680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 246087680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (187/640 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
