-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_165150720_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:40:56.879079+00:00
-- url     : https://prove2.me/submissions/3cd01fe6-0412-438c-9ad2-e0ae1c30ffed

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 63/320]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163184640 142868480 145817600 ⟨⟨76068680866, 76068680873⟩, ⟨73718367788, 78441212650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 163184640 163840000 142868480 145817600 ⟨⟨75744673012, 75744673020⟩, ⟨73402325928, 78109112195⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 162529280 163184640 145817600 148766720 ⟨⟨77524171922, 77524171928⟩, ⟨75168200856, 79902335287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163184640 163840000 145817600 148766720 ⟨⟨77194696483, 77194696490⟩, ⟨74846704871, 79564754506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 163840000 164495360 142868480 145817600 ⟨⟨75422197518, 75422197526⟩, ⟨73087764157, 77778597514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 164495360 165150720 142868480 145817600 ⟨⟨75101240095, 75101240103⟩, ⟨72774668725, 77449653765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163840000 164495360 145817600 148766720 ⟨⟨76866771233, 76866771242⟩, ⟨74526706857, 79228777264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 164495360 165150720 145817600 148766720 ⟨⟨76540381770, 76540381778⟩, ⟨74208192949, 78894388606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 163184640 148766720 151715840 ⟨⟨78976228969, 78976228977⟩, ⟨76614628733, 81359994910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163184640 163840000 148766720 151715840 ⟨⟨78641323699, 78641323707⟩, ⟨76287715963, 81016971973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 162529280 163184640 151715840 154664960 ⟨⟨80424878761, 80424878768⟩, ⟨78057677871, 82814218579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 163184640 163840000 151715840 154664960 ⟨⟨80084581002, 80084581009⟩, ⟨77725385251, 82465791234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163840000 164495360 148766720 151715840 ⟨⟨78307986050, 78307986056⟩, ⟨75962318653, 80675569933⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 164495360 165150720 148766720 151715840 ⟨⟨77976201508, 77976201514⟩, ⟨75638422827, 80335773731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 163840000 164495360 151715840 154664960 ⟨⟨79745867904, 79745867910⟩, ⟨77394625193, 82119001748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 164495360 165150720 151715840 154664960 ⟨⟨79408724846, 79408724852⟩, ⟨77065383616, 81773834963⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 165150720 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 163840000) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 163184640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 163184640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 164495360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 164495360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 163840000) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 163184640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 163184640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 151715840) (by decide) (join_su (m := 164495360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 164495360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
