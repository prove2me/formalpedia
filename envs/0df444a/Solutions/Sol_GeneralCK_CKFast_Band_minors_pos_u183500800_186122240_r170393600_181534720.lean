-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_186122240_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:38:26.716297+00:00
-- url     : https://prove2.me/submissions/828ad5d5-7915-4cec-a7ae-97e45f98a65c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 71/320]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184156160 170393600 173178880 ⟨⟨78297304563, 78297304569⟩, ⟨76174182934, 80438254840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 184156160 184811520 170393600 173178880 ⟨⟨77970973742, 77970973749⟩, ⟨75854293178, 80105395630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 183500800 184156160 173178880 175964160 ⟨⟨79494063416, 79494063422⟩, ⟨77366224345, 81639723082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184156160 184811520 173178880 175964160 ⟨⟨79163285419, 79163285427⟩, ⟨77041898370, 81302406128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 184811520 185466880 170393600 173178880 ⟨⟨77645916926, 77645916931⟩, ⟨75535640511, 79773848024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 185466880 186122240 170393600 173178880 ⟨⟨77322123491, 77322123497⟩, ⟨75218214645, 79443601056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184811520 185466880 173178880 175964160 ⟨⟨78833792847, 78833792850⟩, ⟨76718820932, 80966412160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 185466880 186122240 173178880 175964160 ⟨⟨78505575005, 78505575012⟩, ⟨76396981676, 80631730149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 183500800 184156160 175964160 178749440 ⟨⟨80688809564, 80688809570⟩, ⟨78556267318, 82839164221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184156160 184811520 175964160 178749440 ⟨⟨80353606502, 80353606508⟩, ⟨78227527016, 82497411852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 183500800 184156160 178749440 181534720 ⟨⟨81881555829, 81881555836⟩, ⟨79744324561, 84036591194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 184156160 184811520 178749440 181534720 ⟨⟨81541949622, 81541949628⟩, ⟨79411191639, 83690425545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 184811520 185466880 175964160 178749440 ⟨⟨80019700062, 80019700064⟩, ⟨77900046482, 82156993626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 185466880 186122240 175964160 178749440 ⟨⟨79687079491, 79687079497⟩, ⟨77573815298, 81817898461⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 184811520 185466880 178749440 181534720 ⟨⟨81203651018, 81203651021⟩, ⟨79079329499, 83345604981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 185466880 186122240 178749440 181534720 ⟨⟨80866649207, 80866649213⟩, ⟨78748727668, 83002118361⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 186122240 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 184811520) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 184156160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 184156160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 185466880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 185466880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 184811520) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 184156160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 184156160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 185466880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 185466880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (71/320 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
