-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u196608000_199229440_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:40:54.450532+00:00
-- url     : https://prove2.me/submissions/42d0c021-b51e-404a-8fab-d3b9fb28a407

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [15/64, 19/80]`, `ρ ∈ [469/2560, 243/1280]` by 13 cells of the computing
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
theorem cell0 : cellOK 196608000 197263360 153681920 155074560 ⟨⟨65027124075, 65027124081⟩, ⟨63388535454, 66676623800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 196608000 197263360 155074560 156467200 ⟨⟨65587430258, 65587430264⟩, ⟨63946773583, 67239000615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 197263360 197918720 153681920 155074560 ⟨⟨64751235499, 64751235505⟩, ⟨63116728340, 66396608499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 197263360 197918720 155074560 156467200 ⟨⟨65309365743, 65309365751⟩, ⟨63672795701, 66956804287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 196608000 197263360 156467200 159252480 ⟨⟨66427104572, 66427104578⟩, ⟨64448780748, 68421637551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 197263360 197918720 156467200 159252480 ⟨⟨66145785105, 66145785112⟩, ⟨64173163915, 68134539114⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 197918720 198574080 153681920 155074560 ⟨⟨64476360052, 64476360057⟩, ⟨62845910975, 66117630052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 197918720 198574080 155074560 156467200 ⟨⟨65032320070, 65032320075⟩, ⟨63399813274, 66675650523⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 198574080 199229440 153681920 155074560 ⟨⟨64202489476, 64202489483⟩, ⟨62576075304, 65839679996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 198574080 199229440 155074560 156467200 ⟨⟨64756284944, 64756284951⟩, ⟨63127818215, 66395530829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 197918720 198574080 156467200 159252480 ⟨⟨65865492955, 65865492959⟩, ⟨63898543456, 67848499508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 198574080 199229440 156467200 157859840 ⟨⟨65309675751, 65309675756⟩, ⟨63679158360, 66950975084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 198574080 199229440 157859840 159252480 ⟨⟨65862663080, 65862663088⟩, ⟨64230096920, 67506013950⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 196608000 199229440 153681920 159252480 t = true :=
  ⟨_, (join_su (m := 197918720) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 197263360) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 155074560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 197263360) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 156467200) (by decide) (join_su (m := 198574080) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 155074560) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 198574080) (by decide) (leaf_ok cell10) (join_sr (m := 157859840) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (15/64 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
