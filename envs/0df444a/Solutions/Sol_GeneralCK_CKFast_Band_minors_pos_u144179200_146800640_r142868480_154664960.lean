-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u144179200_146800640_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:29:14.64725+00:00
-- url     : https://prove2.me/submissions/83a2162e-67a1-441d-91a4-d6874a773674

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/64, 7/40]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 144179200 144834560 142868480 145817600 ⟨⟨85827112404, 85827112411⟩, ⟨83230080811, 88450436420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 144834560 145489920 142868480 145817600 ⟨⟨85453597075, 85453597082⟩, ⟨82866248330, 88067072909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 144179200 144834560 145817600 148766720 ⟨⟨87443414909, 87443414917⟩, ⟨84840381677, 90072688174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 144834560 145489920 145817600 148766720 ⟨⟨87063884128, 87063884137⟩, ⟨84470544488, 89683299626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 145489920 146145280 142868480 145817600 ⟨⟨85082097346, 85082097350⟩, ⟨82504360491, 87685797594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146145280 146800640 142868480 145817600 ⟨⟨84712592731, 84712592738⟩, ⟨82144397626, 87306589161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 145489920 146145280 145817600 148766720 ⟨⟨86686390216, 86686390219⟩, ⟨84102673357, 89296020373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 146145280 146800640 145817600 148766720 ⟨⟨86310912550, 86310912557⟩, ⟨83736748478, 88910828976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 144179200 144834560 148766720 151715840 ⟨⟨89055044017, 89055044025⟩, ⟨86446051828, 91690223677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 144834560 145489920 148766720 151715840 ⟨⟨88669548819, 88669548826⟩, ⟨86070260385, 91294861704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 144179200 144834560 151715840 154664960 ⟨⟨90662041136, 90662041143⟩, ⟨88047132134, 93303084877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 144834560 145489920 151715840 154664960 ⟨⟨90270631905, 90270631912⟩, ⟨87665436256, 92901800433⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 145489920 146145280 148766720 151715840 ⟨⟨88286111198, 88286111202⟩, ⟨85696455868, 90901629563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 146145280 146800640 148766720 151715840 ⟨⟨87904710413, 87904710422⟩, ⟨85324618339, 90510505695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 145489920 146145280 151715840 154664960 ⟨⟨89881300422, 89881300424⟩, ⟨87285747633, 92502665808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 146145280 146800640 151715840 154664960 ⟨⟨89494025822, 89494025829⟩, ⟨86908046202, 92105659329⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 144179200 146800640 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 145489920) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 144834560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 144834560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 146145280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 146145280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 145489920) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 144834560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 144834560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 151715840) (by decide) (join_su (m := 146145280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 146145280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/64 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
