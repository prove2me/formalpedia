-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u229376000_230686720_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:57:02.937626+00:00
-- url     : https://prove2.me/submissions/0702acf0-b1c9-466c-af82-78ccf3be4187

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [35/128, 11/40]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 229376000 229703680 131399680 132792320 ⟨⟨45022079144, 45022079151⟩, ⟨44175040455, 45872349320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 229703680 230031360 131399680 132792320 ⟨⟨44920589835, 44920589842⟩, ⟨44074637209, 45769767099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 229376000 229703680 132792320 134184960 ⟨⟨45484211224, 45484211229⟩, ⟨44636174925, 46335480200⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 229703680 230031360 132792320 134184960 ⟨⟨45381732523, 45381732529⟩, ⟨44534783858, 46231907025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230031360 230359040 131399680 132792320 ⟨⟨44819254597, 44819254599⟩, ⟨43974385466, 45667341536⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230359040 230686720 131399680 132792320 ⟨⟨44718072829, 44718072835⟩, ⟨43874284634, 45565072031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 230031360 230359040 132792320 134184960 ⟨⟨45279409072, 45279409074⟩, ⟨44433545469, 46128491688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230359040 230686720 132792320 134184960 ⟨⟨45177240264, 45177240270⟩, ⟨44332459165, 46025233585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 229376000 229703680 134184960 135577600 ⟨⟨45946102444, 45946102451⟩, ⟨45097069065, 46798369689⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 229703680 230031360 134184960 135577600 ⟨⟨45842635867, 45842635872⟩, ⟨44994691685, 46693807079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 229703680 135577600 136970240 ⟨⟨46407753403, 46407753408⟩, ⟨45557723471, 47261018383⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229703680 230031360 135577600 136970240 ⟨⟨46303300456, 46303300461⟩, ⟨45454361279, 47155467854⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 230031360 230359040 134184960 135577600 ⟨⟨45739325707, 45739325710⟩, ⟨44892468150, 46589403480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 230359040 230686720 134184960 135577600 ⟨⟨45636171357, 45636171364⟩, ⟨44790397865, 46485158282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 230031360 230359040 135577600 136970240 ⟨⟨46199005088, 46199005091⟩, ⟨45351154093, 47050077498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230359040 230686720 135577600 136970240 ⟨⟨46094866690, 46094866695⟩, ⟨45248101311, 46944846704⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 229376000 230686720 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 230031360) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 229703680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 229703680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 230359040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 230359040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 230031360) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 229703680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 229703680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 230359040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 230359040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (35/128 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((229376000 : ℤ) : ℝ) / (D : ℝ)) = (35/128 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
