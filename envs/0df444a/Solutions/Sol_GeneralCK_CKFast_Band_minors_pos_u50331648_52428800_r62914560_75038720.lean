-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_52428800_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:57:13.283608+00:00
-- url     : https://prove2.me/submissions/6d4ef4b6-801b-434f-8076-f15a21e3634a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 1/16]`, `ρ ∈ [3/40, 229/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 50855936 62914560 65945600 ⟨⟨94862681266, 94862681278⟩, ⟨89764413874, 100071271935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50855936 51380224 62914560 65945600 ⟨⟨94208151477, 94208151492⟩, ⟨89150095534, 99374941995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 50855936 65945600 68976640 ⟨⟨98627055615, 98627055630⟩, ⟨93522291209, 103840633197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 50855936 51380224 65945600 68976640 ⟨⟨97953475305, 97953475317⟩, ⟨92888746200, 103125468268⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 51380224 51904512 62914560 65945600 ⟨⟨93562534161, 93562534173⟩, ⟨88544025527, 98688224123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 51904512 52428800 62914560 65945600 ⟨⟨92925635011, 92925635026⟩, ⟨87946026086, 98010906420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 51380224 51904512 65945600 68976640 ⟨⟨97288960163, 97288960179⟩, ⟨92263610582, 102420058479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 51904512 52428800 65945600 68976640 ⟨⟨96633314663, 96633314675⟩, ⟨91646704989, 101724191113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 50331648 50855936 68976640 72007680 ⟨⟨102342560747, 102342560759⟩, ⟨97232033225, 107560414779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 50855936 51380224 68976640 72007680 ⟨⟨101650634407, 101650634423⟩, ⟨96579954934, 106827129488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 50331648 50855936 72007680 75038720 ⟨⟨106010556632, 106010556647⟩, ⟨100894960052, 111232016303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 50855936 51380224 72007680 75038720 ⟨⟨105300958000, 105300958012⟩, ⟨100225012137, 110481293486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 51380224 51904512 68976640 72007680 ⟨⟨100967912906, 100967912922⟩, ⟨95936434186, 106103729280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 51904512 52428800 68976640 72007680 ⟨⟨100294199770, 100294199785⟩, ⟨95301290337, 105390000894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 51380224 51904512 72007680 75038720 ⟨⟨104600691668, 104600691680⟩, ⟨99563757846, 109740573414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 51904512 52428800 72007680 75038720 ⟨⟨103909560504, 103909560516⟩, ⟨98911015508, 109009642576⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 52428800 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 51380224) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 50855936) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 50855936) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 65945600) (by decide) (join_su (m := 51904512) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 51904512) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 51380224) (by decide) (join_sr (m := 72007680) (by decide) (join_su (m := 50855936) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 50855936) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 72007680) (by decide) (join_su (m := 51904512) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 51904512) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (1/16 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((52428800 : ℤ) : ℝ) / (D : ℝ)) = (1/16 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
