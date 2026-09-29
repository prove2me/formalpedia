-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_159907840_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:40:08.771074+00:00
-- url     : https://prove2.me/submissions/fdcf8e59-1fb7-4e35-be13-ba3bc70272e5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 61/320]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 157941760 131072000 134021120 ⟨⟨72680007679, 72680007685⟩, ⟨70287401763, 75096016563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157941760 158597120 131072000 134021120 ⟨⟨72366082931, 72366082939⟩, ⟨69981825050, 74773604212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 157941760 134021120 136970240 ⟨⟨74195207745, 74195207754⟩, ⟨71796705503, 76617081126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 157941760 158597120 134021120 136970240 ⟨⟨73875499385, 73875499392⟩, ⟨71485360015, 76288871145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 158597120 159252480 131072000 134021120 ⟨⟨72053731887, 72053731890⟩, ⟨69677764935, 74452823985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 159252480 159907840 131072000 134021120 ⟨⟨71742939289, 71742939297⟩, ⟨69375206779, 74133660001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 158597120 159252480 134021120 136970240 ⟨⟨73557385311, 73557385314⟩, ⟨71175551758, 75962313807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159252480 159907840 134021120 136970240 ⟨⟨73240850125, 73240850133⟩, ⟨70867265952, 75637393093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 157941760 136970240 139919360 ⟨⟨75706532681, 75706532688⟩, ⟨73302167892, 78134236574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 157941760 158597120 136970240 139919360 ⟨⟨75381083751, 75381083758⟩, ⟨72985096186, 77800272494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 157941760 139919360 142868480 ⟨⟨77214013997, 77214014005⟩, ⟨74803820071, 79647514801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 157941760 158597120 139919360 142868480 ⟨⟨76882867048, 76882867056⟩, ⟨74481064218, 79307839651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 158597120 159252480 136970240 139919360 ⟨⟨75057249223, 75057249225⟩, ⟨72669581883, 77467981103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 159252480 159907840 136970240 139919360 ⟨⟨74735013564, 74735013571⟩, ⟨72355610066, 77137346248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 158597120 159252480 139919360 142868480 ⟨⟨76553354156, 76553354160⟩, ⟨74159885487, 78969856769⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 159252480 159907840 139919360 142868480 ⟨⟨76225459661, 76225459668⟩, ⟨73840268830, 78633549874⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 159907840 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 158597120) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 157941760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 157941760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 159252480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 159252480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 158597120) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 157941760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 157941760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 159252480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 159252480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (61/320 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
