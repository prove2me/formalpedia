-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_165150720_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:47:18.796861+00:00
-- url     : https://prove2.me/submissions/bbe5fc5b-075d-4239-9428-4cbf878dbbf5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 63/320]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163184640 154664960 157614080 ⟨⟨81870147799, 81870147807⟩, ⟨79497374476, 84265033091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 163184640 163840000 154664960 157614080 ⟨⟨81524494490, 81524494496⟩, ⟨79159738541, 83911238676⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 163184640 157614080 160563200 ⟨⟨83312062343, 83312062349⟩, ⟨80933744511, 85712465002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163184640 163840000 157614080 160563200 ⟨⟨82961090015, 82961090023⟩, ⟨80590801402, 85353340448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 163840000 164495360 154664960 157614080 ⟨⟨81180442491, 81180442499⟩, ⟨78823651892, 83559098694⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 164495360 165150720 154664960 157614080 ⟨⟨80837977089, 80837977095⟩, ⟨78489100341, 83208597890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163840000 164495360 157614080 160563200 ⟨⟨82611735276, 82611735282⟩, ⟨80249423927, 84995886517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 164495360 165150720 157614080 160563200 ⟨⟨82263983310, 82263983317⟩, ⟨79909597800, 84640087859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 163184640 160563200 163512320 ⟨⟨84750648403, 84750648411⟩, ⟨82366813699, 87156540617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163184640 163840000 160563200 163512320 ⟨⟨84394393200, 84394393209⟩, ⟨82018599170, 86792122454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 162529280 163184640 163512320 166461440 ⟨⟨86185931756, 86185931762⟩, ⟨83796607529, 88597285999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 163184640 163840000 163512320 166461440 ⟨⟨85824429428, 85824429434⟩, ⟨83443156945, 88227610360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163840000 164495360 160563200 163512320 ⟨⟨84039771486, 84039771493⟩, ⟨81671966251, 86429390726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 164495360 165150720 160563200 163512320 ⟨⟨83686768356, 83686768363⟩, ⟨81326900566, 86068329993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 163840000 164495360 163512320 166461440 ⟨⟨85464576121, 85464576129⟩, ⟨83091303588, 87859636596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 164495360 165150720 163512320 166461440 ⟨⟨85106356846, 85106356854⟩, ⟨82741032990, 87493349183⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 165150720 154664960 166461440 t = true :=
  ⟨_, (join_sr (m := 160563200) (by decide) (join_su (m := 163840000) (by decide) (join_sr (m := 157614080) (by decide) (join_su (m := 163184640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 163184640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 157614080) (by decide) (join_su (m := 164495360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 164495360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 163840000) (by decide) (join_sr (m := 163512320) (by decide) (join_su (m := 163184640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 163184640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163512320) (by decide) (join_su (m := 164495360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 164495360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
