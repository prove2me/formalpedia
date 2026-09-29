-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u102236160_104857600_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:37:34.354835+00:00
-- url     : https://prove2.me/submissions/1e5facfc-2c10-4e36-93b6-844dc4055391

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/320, 1/8]`, `ρ ∈ [137/1280, 73/640]` by 10 cells of the computing
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
theorem cell0 : cellOK 102236160 102891520 89784320 92733440 ⟨⟨76435108326, 76435108334⟩, ⟨73149176040, 79766376786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 102891520 103546880 89784320 92733440 ⟨⟨76031001940, 76031001944⟩, ⟨72761840106, 79345080938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 102236160 102891520 92733440 95682560 ⟨⟨78680323554, 78680323564⟩, ⟨75386192944, 82019585575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 102891520 103546880 92733440 95682560 ⟨⟨78266245639, 78266245641⟩, ⟨74988898053, 81588310103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 103546880 104202240 89784320 91258880 ⟨⟨75072141242, 75072141250⟩, ⟨72539816473, 77631416313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 103546880 104202240 91258880 92733440 ⟨⟨76187756855, 76187756864⟩, ⟨73651854730, 78750560511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 104202240 104857600 89784320 91258880 ⟨⟨74677318863, 74677318871⟩, ⟨72156990968, 77224363583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 104202240 104857600 91258880 92733440 ⟨⟨75787971611, 75787971621⟩, ⟨73264073402, 78338539033⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 103546880 104202240 92733440 95682560 ⟨⟨77855651844, 77855651854⟩, ⟨74594909500, 81160702558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 104202240 104857600 92733440 95682560 ⟨⟨77448492080, 77448492090⟩, ⟨74204180073, 80736709827⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 102236160 104857600 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 103546880) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 102891520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 102891520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 92733440) (by decide) (join_su (m := 104202240) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 91258880) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 104202240) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/320 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((102236160 : ℤ) : ℝ) / (D : ℝ)) = (39/320 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
