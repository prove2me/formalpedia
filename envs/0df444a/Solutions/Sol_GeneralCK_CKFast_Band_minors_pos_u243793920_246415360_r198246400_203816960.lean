-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r198246400_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:19:46.36912+00:00
-- url     : https://prove2.me/submissions/3ace926d-efa2-4943-9d90-77aca7127f07

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [121/512, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 198246400 199639040 ⟨⟨60571485072, 60571485074⟩, ⟨59122423206, 62029092821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 243793920 244449280 199639040 201031680 ⟨⟨60982454045, 60982454048⟩, ⟨59531690006, 62441769571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 244449280 245104640 198246400 199639040 ⟨⟨60293590659, 60293590665⟩, ⟨58847474364, 61748226346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 199639040 201031680 ⟨⟨60702786403, 60702786408⟩, ⟨59254972165, 62159125665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 243793920 244449280 201031680 202424320 ⟨⟨61393261208, 61393261209⟩, ⟨59940795269, 62854284228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 243793920 244449280 202424320 203816960 ⟨⟨61803906935, 61803906937⟩, ⟨60349739371, 63266637167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 244449280 245104640 201031680 202424320 ⟨⟨61111822409, 61111822416⟩, ⟨59662310490, 62569864977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 244449280 245104640 202424320 203816960 ⟨⟨61520699050, 61520699056⟩, ⟨60069489709, 62980444653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 245104640 245760000 198246400 199639040 ⟨⟨60016381594, 60016381600⟩, ⟨58573197412, 61468058836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 245104640 245760000 199639040 201031680 ⟨⟨60423807043, 60423807050⟩, ⟨58978929146, 61877183661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245760000 246415360 198246400 199639040 ⟨⟨59739852942, 59739852947⟩, ⟨58299587507, 61188585262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245760000 246415360 199639040 201031680 ⟨⟨60145511016, 60145511022⟩, ⟨58703556092, 61595938514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 201031680 202424320 ⟨⟨60831074809, 60831074815⟩, ⟨59384503444, 62286150545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245104640 245760000 202424320 203816960 ⟨⟨61238185255, 61238185262⟩, ⟨59789920672, 62694959854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245760000 246415360 201031680 202424320 ⟨⟨60551013439, 60551013445⟩, ⟨59107369260, 62003135871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 202424320 203816960 ⟨⟨60956360569, 60956360575⟩, ⟨59511027370, 62410177692⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 198246400 203816960 t = true :=
  ⟨_, (join_su (m := 245104640) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 244449280) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 199639040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 244449280) (by decide) (join_sr (m := 202424320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202424320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 201031680) (by decide) (join_su (m := 245760000) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 199639040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245760000) (by decide) (join_sr (m := 202424320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 202424320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (121/512 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
