-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u170393600_173015040_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:14:50.586307+00:00
-- url     : https://prove2.me/submissions/49f163e0-eb95-44b3-b5ff-92e9b0606ecf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/64, 33/160]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 170393600 171048960 125829120 127221760 ⟨⟨63809268231, 63809268237⟩, ⟨62031912480, 65599704543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 170393600 171048960 127221760 128614400 ⟨⟨64475343407, 64475343414⟩, ⟨62695633105, 66268133148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 171048960 171704320 125829120 127221760 ⟨⟨63535254802, 63535254810⟩, ⟨61762999847, 65320524827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 171048960 171704320 127221760 128614400 ⟨⟨64198742770, 64198742776⟩, ⟨62424139525, 65986360105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 170393600 171048960 128614400 130007040 ⟨⟨65140714544, 65140714552⟩, ⟨63358653897, 66935853474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 170393600 171048960 130007040 131399680 ⟨⟨65805384128, 65805384135⟩, ⟨64020977321, 67602868023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 171048960 171704320 128614400 130007040 ⟨⟨64861534638, 64861534644⟩, ⟨63084587242, 66651495107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 171048960 171704320 130007040 131399680 ⟨⟨65523632853, 65523632859⟩, ⟨63744345428, 67315932299⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 171704320 172359680 125829120 127221760 ⟨⟨63262505631, 63262505634⟩, ⟨61495317532, 65042643885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 171704320 172359680 127221760 128614400 ⟨⟨63923415282, 63923415285⟩, ⟨62153885153, 65705894727⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 172359680 173015040 125829120 127221760 ⟨⟨62991009052, 62991009058⟩, ⟨61228854220, 64766049708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 172359680 173015040 127221760 128614400 ⟨⟨63649349218, 63649349226⟩, ⟨61884858611, 65426724949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 171704320 172359680 128614400 130007040 ⟨⟨64583636688, 64583636691⟩, ⟨62811768603, 66368453215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 171704320 172359680 130007040 131399680 ⟨⟨65243172255, 65243172258⟩, ⟨63468970270, 67030321771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 172359680 173015040 128614400 130007040 ⟨⟨64307008908, 64307008915⟩, ⟨62540186535, 66086715668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 172359680 173015040 130007040 131399680 ⟨⟨64963990490, 64963990498⟩, ⟨63194840347, 66746024249⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 170393600 173015040 125829120 131399680 t = true :=
  ⟨_, (join_su (m := 171704320) (by decide) (join_sr (m := 128614400) (by decide) (join_su (m := 171048960) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 127221760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 171048960) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 130007040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 128614400) (by decide) (join_su (m := 172359680) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 127221760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 172359680) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 130007040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/64 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
