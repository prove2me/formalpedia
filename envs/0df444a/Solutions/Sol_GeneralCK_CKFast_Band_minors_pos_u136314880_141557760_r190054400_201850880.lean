-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_141557760_r190054400_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:34:25.487133+00:00
-- url     : https://prove2.me/submissions/798488a9-3da6-4dd6-8687-4fe92afeabe2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 27/160]`, `ρ ∈ [29/128, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 137625600 190054400 193003520 ⟨⟨116657694308, 116657694315⟩, ⟨112189065459, 121195497017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 137625600 193003520 195952640 ⟨⟨118265554567, 118265554574⟩, ⟨113787122913, 122813026755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 137625600 138936320 190054400 193003520 ⟨⟨115676181343, 115676181353⟩, ⟨111238236712, 120182541340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 137625600 138936320 193003520 195952640 ⟨⟨117273195628, 117273195635⟩, ⟨112825454207, 121789225161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 137625600 195952640 198901760 ⟨⟨119868841571, 119868841578⟩, ⟨115380668703, 124425921121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 137625600 198901760 201850880 ⟨⟨121467596631, 121467596640⟩, ⟨116969743377, 126034222196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 137625600 138936320 195952640 198901760 ⟨⟨118865729797, 118865729804⟩, ⟨114408251690, 123391368224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 137625600 138936320 198901760 201850880 ⟨⟨120453823956, 120453823963⟩, ⟨115986668536, 124989011374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 138936320 140247040 190054400 193003520 ⟨⟨114704837726, 114704837734⟩, ⟨110297124086, 119180222440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 138936320 140247040 193003520 195952640 ⟨⟨116291061879, 116291061888⟩, ⟨111873559131, 120776114327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 140247040 141557760 190054400 193003520 ⟨⟨113743464370, 113743464375⟩, ⟨109365538520, 118188330851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 140247040 141557760 193003520 195952640 ⟨⟨115318953945, 115318953950⟩, ⟨110931248258, 119773484575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 138936320 140247040 195952640 198901760 ⟨⟨117872897229, 117872897236⟩, ⟨113445664020, 122367558213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 138936320 140247040 198901760 201850880 ⟨⟨119450382712, 119450382720⟩, ⟨115013476983, 123954593750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 140247040 141557760 195952640 198901760 ⟨⟨116890144239, 116890144241⟩, ⟨112492715930, 121354281239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140247040 141557760 198901760 201850880 ⟨⟨118457073052, 118457073058⟩, ⟨114049978660, 122930759341⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 141557760 190054400 201850880 t = true :=
  ⟨_, (join_su (m := 138936320) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 137625600) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 193003520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 137625600) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 198901760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 195952640) (by decide) (join_su (m := 140247040) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 193003520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 140247040) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 198901760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (29/128 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
