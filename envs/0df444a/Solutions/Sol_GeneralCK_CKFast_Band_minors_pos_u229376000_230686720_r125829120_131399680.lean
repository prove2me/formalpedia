-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u229376000_230686720_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:56:42.492975+00:00
-- url     : https://prove2.me/submissions/fe5e253e-443e-4562-b908-8d87537cdf3c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [35/128, 11/40]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 229376000 229703680 125829120 127221760 ⟨⟨43171130328, 43171130333⟩, ⟨42328087398, 44017399935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 229703680 230031360 125829120 127221760 ⟨⟨43073613811, 43073613817⟩, ⟨42231650598, 43918796823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 229376000 229703680 127221760 128614400 ⟨⟨43634231804, 43634231810⟩, ⟨42790189133, 44481502360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 229703680 230031360 127221760 128614400 ⟨⟨43535719795, 43535719801⟩, ⟨42692758437, 44381902168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230031360 230359040 125829120 127221760 ⟨⟨42976246573, 42976246576⟩, ⟨42135360516, 43820345570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230359040 230686720 125829120 127221760 ⟨⟨42879028029, 42879028036⟩, ⟨42039216581, 43722045591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 230031360 230359040 127221760 128614400 ⟨⟨43437358275, 43437358278⟩, ⟨42595475668, 44282455045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 230359040 230686720 127221760 128614400 ⟨⟨43339146656, 43339146661⟩, ⟨42498340248, 44183160406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 229376000 229703680 128614400 130007040 ⟨⟨44097090032, 44097090039⟩, ⟨43252048156, 44945360999⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 229703680 230031360 128614400 130007040 ⟨⟨43997584065, 43997584070⟩, ⟨43153625090, 44844765265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 229376000 229703680 130007040 131399680 ⟨⟨44559705613, 44559705619⟩, ⟨43713665064, 45408976452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 229703680 230031360 130007040 131399680 ⟨⟨44459207213, 44459207219⟩, ⟨43614251150, 45307386709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 230031360 230359040 128614400 130007040 ⟨⟨43898229786, 43898229789⟩, ⟨43055351151, 44744323804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 230359040 230686720 128614400 130007040 ⟨⟨43799026608, 43799026614⟩, ⟨42957225757, 44644036027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 230031360 230359040 130007040 131399680 ⟨⟨44358861697, 44358861700⟩, ⟨43514987554, 45205952438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 230359040 230686720 130007040 131399680 ⟨⟨44258668471, 44258668476⟩, ⟨43415873692, 45104673040⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 229376000 230686720 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 230031360) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 229703680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 229703680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 230359040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 230359040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 230031360) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 229703680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 229703680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 230359040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 230359040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (35/128 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((229376000 : ℤ) : ℝ) / (D : ℝ)) = (35/128 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
