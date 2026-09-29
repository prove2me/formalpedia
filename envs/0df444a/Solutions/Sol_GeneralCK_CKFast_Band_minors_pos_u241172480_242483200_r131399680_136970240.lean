-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_242483200_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:25:08.417763+00:00
-- url     : https://prove2.me/submissions/833d5947-692f-4696-8153-8d8c6c1f712d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 37/128]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241500160 131399680 132792320 ⟨⟨41461430568, 41461430575⟩, ⟨40651940421, 42273919702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241500160 241827840 131399680 132792320 ⟨⟨41365130989, 41365130991⟩, ⟨40556640384, 42176614510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241500160 132792320 134184960 ⟨⟨41888659671, 41888659677⟩, ⟨41078227197, 42702092551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241500160 241827840 132792320 134184960 ⟨⟨41791410752, 41791410754⟩, ⟨40981979319, 42603836524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241827840 242155520 131399680 132792320 ⟨⟨41268965618, 41268965624⟩, ⟨40461472318, 42079445790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 242155520 242483200 131399680 132792320 ⟨⟨41172933951, 41172933957⟩, ⟨40366435726, 41982413022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242155520 132792320 134184960 ⟨⟨41694297087, 41694297092⟩, ⟨40885864455, 42505718020⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242155520 242483200 132792320 134184960 ⟨⟨41597318169, 41597318175⟩, ⟨40789882107, 42407736510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241500160 134184960 135577600 ⟨⟨42315697623, 42315697629⟩, ⟨41504323146, 43130073920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241500160 241827840 134184960 135577600 ⟨⟨42217500612, 42217500614⟩, ⟨41407128670, 43030868314⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 241500160 135577600 136970240 ⟨⟨42742544867, 42742544872⟩, ⟨41930228709, 43557864256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 241500160 241827840 135577600 136970240 ⟨⟨42643401009, 42643401012⟩, ⟨41832088876, 43457710320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 241827840 242155520 134184960 135577600 ⟨⟨42119439896, 42119439901⟩, ⟨41310068247, 42931801271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242155520 242483200 134184960 135577600 ⟨⟨42021514962, 42021514968⟩, ⟨41213141372, 42832872262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 241827840 242155520 135577600 136970240 ⟨⟨42544394480, 42544394485⟩, ⟨41734084126, 43357695982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 242155520 242483200 135577600 136970240 ⟨⟨42445524761, 42445524767⟩, ⟨41636213953, 43257820709⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 242483200 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 241500160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241500160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 242155520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 241827840) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 241500160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 241500160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 242155520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (37/128 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
