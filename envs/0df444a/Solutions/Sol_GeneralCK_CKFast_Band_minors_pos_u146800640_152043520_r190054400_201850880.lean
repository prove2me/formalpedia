-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_152043520_r190054400_201850880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:48:13.584905+00:00
-- url     : https://prove2.me/submissions/dbedb7d8-e863-4350-9cd3-c896c3c19016

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 29/160]`, `ρ ∈ [29/128, 77/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 148111360 190054400 193003520 ⟨⟨109079534383, 109079534387⟩, ⟨104844230482, 113378322657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 146800640 148111360 193003520 195952640 ⟨⟨110602173224, 110602173228⟩, ⟨106357157231, 114910583696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 148111360 149422080 190054400 193003520 ⟨⟨108174078419, 108174078426⟩, ⟨103966097972, 112444888961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 149422080 193003520 195952640 ⟨⟨109686309167, 109686309175⟩, ⟨105468634006, 113966729206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 146800640 148111360 195952640 198901760 ⟨⟨112120934819, 112120934821⟩, ⟨107866257188, 116438916445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 146800640 148111360 198901760 201850880 ⟨⟨113635851794, 113635851798⟩, ⟨109371562420, 117963354101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 148111360 149422080 195952640 198901760 ⟨⟨111194742205, 111194742212⟩, ⟨106967421508, 115484721967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 148111360 149422080 198901760 201850880 ⟨⟨112699409213, 112699409222⟩, ⟨108462491621, 116998899479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 149422080 150732800 190054400 193003520 ⟨⟨107277334123, 107277334130⟩, ⟨103096296469, 111520559225⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 149422080 150732800 193003520 195952640 ⟨⟨108779209960, 108779209969⟩, ⟨104588496111, 113032030566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 150732800 152043520 190054400 193003520 ⟨⟨106389139166, 106389139173⟩, ⟨102234671602, 110605162878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 150732800 152043520 193003520 195952640 ⟨⟨107880712901, 107880712909⟩, ⟨103716588745, 112106316898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 150732800 195952640 198901760 ⟨⟨110277366077, 110277366084⟩, ⟨106077023959, 114539733666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 149422080 150732800 198901760 201850880 ⟨⟨111771833239, 111771833246⟩, ⟨107561910260, 116043699815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 150732800 152043520 195952640 198901760 ⟨⟨109368643391, 109368643398⟩, ⟨105194909343, 113603780376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 150732800 152043520 198901760 201850880 ⟨⟨110852960508, 110852960517⟩, ⟨106669662773, 115097583694⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 152043520 190054400 201850880 t = true :=
  ⟨_, (join_su (m := 149422080) (by decide) (join_sr (m := 195952640) (by decide) (join_su (m := 148111360) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 193003520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 148111360) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 198901760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 195952640) (by decide) (join_su (m := 150732800) (by decide) (join_sr (m := 193003520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 193003520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 150732800) (by decide) (join_sr (m := 198901760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 198901760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (29/128 : ℝ) (77/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  have e3 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
