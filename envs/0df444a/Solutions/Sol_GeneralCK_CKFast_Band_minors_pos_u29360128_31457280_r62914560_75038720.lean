-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u29360128_31457280_r62914560_75038720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:21:30.131924+00:00
-- url     : https://prove2.me/submissions/96e98c5d-8de3-4be0-91c2-70a4da54908a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/200, 3/80]`, `ρ ∈ [3/40, 229/2560]` by 10 cells of the computing
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
theorem cell0 : cellOK 29360128 29884416 62914560 65945600 ⟨⟨131641090520, 131641090542⟩, ⟨124095152095, 139410432784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 29884416 30408704 62914560 65945600 ⟨⟨130361503323, 130361503340⟩, ⟨122906847297, 138034810987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 29360128 30408704 65945600 68976640 ⟨⟨135642330249, 135642330266⟩, ⟨124921983340, 146818484778⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 30408704 30932992 62914560 65945600 ⟨⟨129107906660, 129107906681⟩, ⟨121742255922, 136687612479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 30932992 31457280 62914560 65945600 ⟨⟨127879466377, 127879466394⟩, ⟨120600628186, 135367911908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 30408704 31457280 65945600 68976640 ⟨⟨133084891967, 133084891984⟩, ⟨122611686492, 143995477055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 29360128 30408704 68976640 72007680 ⟨⟨140195058399, 140195058421⟩, ⟨129490789413, 151345135844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 29360128 30408704 72007680 75038720 ⟨⟨144659910580, 144659910598⟩, ⟨133973315756, 155782602997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 30408704 31457280 68976640 72007680 ⟨⟨137590696169, 137590696191⟩, ⟨127130536909, 148478941180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 30408704 31457280 72007680 75038720 ⟨⟨142011530846, 142011530868⟩, ⟨131566001594, 152876109783⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 29360128 31457280 62914560 75038720 t = true :=
  ⟨_, (join_sr (m := 68976640) (by decide) (join_su (m := 30408704) (by decide) (join_sr (m := 65945600) (by decide) (join_su (m := 29884416) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 65945600) (by decide) (join_su (m := 30932992) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 30408704) (by decide) (join_sr (m := 72007680) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 72007680) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/200 : ℝ) (3/80 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e1 : (((31457280 : ℤ) : ℝ) / (D : ℝ)) = (3/80 : ℝ) := by norm_num [D]
  have e2 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e3 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
