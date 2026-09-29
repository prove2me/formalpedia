-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_229376000_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:56:51.575834+00:00
-- url     : https://prove2.me/submissions/de29a76f-8c45-4918-a84e-bff85ffcb5b3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 35/128]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 228065280 228392960 131399680 132792320 ⟨⟨45429589054, 45429589060⟩, ⟨44578180220, 46284257009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228392960 228720640 131399680 132792320 ⟨⟨45327477472, 45327477474⟩, ⟨44477165076, 46181042040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228065280 228392960 132792320 134184960 ⟨⟨45895690552, 45895690557⟩, ⟨45043277807, 46751363579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228392960 228720640 132792320 134184960 ⟨⟨45792584828, 45792584831⟩, ⟨44941270101, 46647152899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228720640 229048320 131399680 132792320 ⟨⟨45225522360, 45225522367⟩, ⟨44376303795, 46077986182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 229048320 229376000 131399680 132792320 ⟨⟨45123723119, 45123723126⟩, ⟨44275595787, 45975088811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228720640 229048320 132792320 134184960 ⟨⟨45689636770, 45689636776⟩, ⟨44839417449, 46543102523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229048320 229376000 132792320 134184960 ⟨⟨45586845770, 45586845777⟩, ⟨44737719258, 46439211829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 228392960 134184960 135577600 ⟨⟨46361545058, 46361545063⟩, ⟨45508128957, 47218222599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228392960 228720640 134184960 135577600 ⟨⟨46257446740, 46257446743⟩, ⟨45405130229, 47113017759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 228392960 135577600 136970240 ⟨⟨46827153187, 46827153193⟩, ⟨45972734286, 47684834683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228392960 228720640 135577600 136970240 ⟨⟨46722063814, 46722063817⟩, ⟨45868746067, 47578637231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 228720640 229048320 134184960 135577600 ⟨⟨46153507271, 46153507278⟩, ⟨45302287736, 47007974412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 229048320 229376000 134184960 135577600 ⟨⟨46049726044, 46049726049⟩, ⟨45199600884, 46903091928⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228720640 229048320 135577600 136970240 ⟨⟨46617134468, 46617134474⟩, ⟨45764915261, 47472602451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 229048320 229376000 135577600 136970240 ⟨⟨46512364536, 46512364542⟩, ⟨45661241266, 47366729708⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 229376000 131399680 136970240 t = true :=
  ⟨_, (join_sr (m := 134184960) (by decide) (join_su (m := 228720640) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 228392960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 228392960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 132792320) (by decide) (join_su (m := 229048320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 229048320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 228720640) (by decide) (join_sr (m := 135577600) (by decide) (join_su (m := 228392960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 228392960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 135577600) (by decide) (join_su (m := 229048320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 229048320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (35/128 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((229376000 : ℤ) : ℝ) / (D : ℝ)) = (35/128 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
