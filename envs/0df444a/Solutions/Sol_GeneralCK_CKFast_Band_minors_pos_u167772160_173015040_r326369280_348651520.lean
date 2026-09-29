-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r326369280_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:47.998383+00:00
-- url     : https://prove2.me/submissions/45431238-e514-4974-b8dc-32b916c18afc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [249/640, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 326369280 331939840 ⟨⟨156467670253, 156467670260⟩, ⟨151407677728, 161602924581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 169082880 170393600 326369280 331939840 ⟨⟨155289669460, 155289669469⟩, ⟨150259909846, 160394100023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 169082880 331939840 337510400 ⟨⟨158831262073, 158831262082⟩, ⟨153754983896, 163982594925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 169082880 170393600 331939840 337510400 ⟨⟨157639274759, 157639274766⟩, ⟨152593218860, 162759803228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 170393600 171704320 326369280 331939840 ⟨⟨154119413141, 154119413150⟩, ⟨149119579741, 159193333653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 171704320 173015040 326369280 331939840 ⟨⟨152956786990, 152956786998⟩, ⟨147986577953, 158000506212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 171704320 331939840 337510400 ⟨⟨156455048472, 156455048479⟩, ⟨151438910741, 161545083476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 171704320 173015040 331939840 337510400 ⟨⟨155278469289, 155278469298⟩, ⟨150291950381, 160338316876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 169082880 337510400 343080960 ⟨⟨161187851536, 161187851544⟩, ⟨156095384224, 166355164853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 169082880 170393600 337510400 343080960 ⟨⟨159982007670, 159982007679⟩, ⟨154919749846, 165118538134⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 169082880 343080960 348651520 ⟨⟨163537533487, 163537533496⟩, ⟨158428971907, 168720730884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 169082880 170393600 343080960 348651520 ⟨⟨162317960703, 162317960710⟩, ⟨157239593707, 167470398864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 170393600 171704320 337510400 343080960 ⟨⟨158783939437, 158783939446⟩, ⟨153751589594, 163889995148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 171704320 173015040 337510400 343080960 ⟨⟨157593533322, 157593533332⟩, ⟨152590794644, 162669417590⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 170393600 171704320 343080960 348651520 ⟨⟨161106176258, 161106176267⟩, ⟨156057704970, 166228160448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 171704320 173015040 343080960 348651520 ⟨⟨159902067072, 159902067080⟩, ⟨154883197226, 164993897845⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 326369280 348651520 t = true :=
  ⟨_, (join_sr (m := 337510400) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 169082880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 331939840) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 171704320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 170393600) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 169082880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 343080960) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 171704320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
