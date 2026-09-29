-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_110100480_r201850880_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:31:34.115221+00:00
-- url     : https://prove2.me/submissions/07f17eb7-cebb-4ccb-9b36-546a57255b71

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 21/160]`, `ρ ∈ [77/320, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 106168320 201850880 207749120 ⟨⟨152319056010, 152319056021⟩, ⟨145458387773, 159326215653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 106168320 107479040 201850880 207749120 ⟨⟨150962741315, 150962741325⟩, ⟨144163411657, 157906530065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 106168320 207749120 213647360 ⟨⟨156016612255, 156016612266⟩, ⟨149137657946, 163040707915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 106168320 107479040 207749120 213647360 ⟨⟨154637334098, 154637334107⟩, ⟨147819486191, 161598339141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 107479040 108789760 201850880 207749120 ⟨⟨149623743566, 149623743568⟩, ⟨142884695970, 156505261800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 108789760 110100480 201850880 207749120 ⟨⟨148301666658, 148301666669⟩, ⟨141621872155, 155121985953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 107479040 108789760 207749120 213647360 ⟨⟨153275452719, 153275452725⟩, ⟨146517669119, 160174451394⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 108789760 110100480 207749120 213647360 ⟨⟨151930573859, 151930573868⟩, ⟨145231839367, 158768622324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 106168320 213647360 219545600 ⟨⟨159686085591, 159686085602⟩, ⟨152789338195, 166726633109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 106168320 107479040 213647360 219545600 ⟨⟨158284394119, 158284394129⟩, ⟨151448511964, 165262139501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 104857600 106168320 219545600 225443840 ⟨⟨163328099418, 163328099429⟩, ⟨156414034003, 170384632607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 106168320 107479040 219545600 225443840 ⟨⟨161904526589, 161904526598⟩, ⟨155051076869, 168898553730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 107479040 108789760 213647360 219545600 ⟨⟨156900168758, 156900168765⟩, ⟨150124124204, 163816180134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 108789760 110100480 213647360 219545600 ⟨⟨155533017286, 155533017297⟩, ⟨148815808951, 162388335403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 107479040 108789760 219545600 225443840 ⟨⟨160498479257, 160498479263⟩, ⟨153704632065, 167431052396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 108789760 110100480 219545600 225443840 ⟨⟨159109567419, 159109567428⟩, ⟨152374335222, 165981711901⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 110100480 201850880 225443840 t = true :=
  ⟨_, (join_sr (m := 213647360) (by decide) (join_su (m := 107479040) (by decide) (join_sr (m := 207749120) (by decide) (join_su (m := 106168320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 106168320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 207749120) (by decide) (join_su (m := 108789760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 108789760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 107479040) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 106168320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 106168320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 219545600) (by decide) (join_su (m := 108789760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 108789760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (77/320 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
