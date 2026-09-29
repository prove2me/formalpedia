-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_138936320_r95682560_101580800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:08:27.477256+00:00
-- url     : https://prove2.me/submissions/70eca3d6-db46-4624-9c73-742b9109b122

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 53/320]`, `ρ ∈ [73/640, 31/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 136970240 95682560 97157120 ⟨⟨62216140597, 62216140606⟩, ⟨60146264142, 64304356309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136314880 136970240 97157120 98631680 ⟨⟨63109123699, 63109123706⟩, ⟨61036172953, 65200399894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136970240 137625600 95682560 97157120 ⟨⟨61927696177, 61927696184⟩, ⟨59865311658, 64008298828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 136970240 137625600 97157120 98631680 ⟨⟨62816994844, 62816994851⟩, ⟨60751545134, 64900649274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 136314880 136970240 98631680 100106240 ⟨⟨64000539779, 64000539787⟩, ⟨61924526675, 66094864460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 136314880 136970240 100106240 101580800 ⟨⟨64890396563, 64890396571⟩, ⟨62811332956, 66987757814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 136970240 137625600 98631680 100106240 ⟨⟨63704744904, 63704744912⟩, ⟨61636241757, 65791439293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 136970240 137625600 100106240 101580800 ⟨⟨64590953949, 64590953956⟩, ⟨62519409039, 66680676563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 137625600 138280960 95682560 97157120 ⟨⟨61641061859, 61641061866⟩, ⟨59586106908, 63714115180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 137625600 138280960 97157120 98631680 ⟨⟨62526693938, 62526693945⟩, ⟨60468682903, 64602790318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 138280960 138936320 95682560 97157120 ⟨⟨61356217045, 61356217052⟩, ⟨59308630086, 63421783956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 138280960 138936320 97157120 98631680 ⟨⟨62238200226, 62238200232⟩, ⟨60187566292, 64306801466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 137625600 138280960 98631680 100106240 ⟨⟨63410795594, 63410795602⟩, ⟨61349740049, 65489923393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 137625600 138280960 100106240 101580800 ⟨⟨64293374291, 64293374299⟩, ⟨62229285736, 66375521950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 138280960 138936320 98631680 100106240 ⟨⟨63118670943, 63118670951⟩, ⟨61065001436, 65190295048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 138280960 138936320 100106240 101580800 ⟨⟨63997636535, 63997636542⟩, ⟨61940942778, 66072272117⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 138936320 95682560 101580800 t = true :=
  ⟨_, (join_su (m := 137625600) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 136970240) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 97157120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 136970240) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 100106240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 98631680) (by decide) (join_su (m := 138280960) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 97157120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 138280960) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 100106240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (53/320 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (31/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
