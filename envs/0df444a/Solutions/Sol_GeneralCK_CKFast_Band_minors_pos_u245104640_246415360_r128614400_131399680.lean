-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u245104640_246415360_r128614400_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:28:45.087708+00:00
-- url     : https://prove2.me/submissions/3e4a5868-965a-4d40-a8a4-2f4ede14ee57

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [187/640, 47/160]`, `ρ ∈ [157/1024, 401/2560]` by 8 cells of the computing
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
theorem cell0 : cellOK 245104640 245432320 128614400 130007040 ⟨⟨39482240550, 39482240555⟩, ⟨38686448703, 40280956907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 245432320 245760000 128614400 130007040 ⟨⟨39389395913, 39389395918⟩, ⟨38594574322, 40187136173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 245104640 245432320 130007040 131399680 ⟨⟨39898500283, 39898500289⟩, ⟨39101783432, 40698143132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 245432320 245760000 130007040 131399680 ⟨⟨39804716287, 39804716292⟩, ⟨39008971175, 40603381559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245760000 246087680 128614400 130007040 ⟨⟨39296677486, 39296677492⟩, ⟨38502824011, 40093443808⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246087680 246415360 128614400 130007040 ⟨⟨39204084792, 39204084797⟩, ⟨38411197300, 39999879325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245760000 246087680 130007040 131399680 ⟨⟨39711059518, 39711059523⟩, ⟨38916284003, 40508749373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 246087680 246415360 130007040 131399680 ⟨⟨39617529496, 39617529502⟩, ⟨38823721446, 40414246086⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 245104640 246415360 128614400 131399680 t = true :=
  ⟨_, (join_su (m := 245760000) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 245432320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 245432320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 130007040) (by decide) (join_su (m := 246087680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 246087680) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (187/640 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (157/1024 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((245104640 : ℤ) : ℝ) / (D : ℝ)) = (187/640 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((128614400 : ℤ) : ℝ) / (D : ℝ)) = (157/1024 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
