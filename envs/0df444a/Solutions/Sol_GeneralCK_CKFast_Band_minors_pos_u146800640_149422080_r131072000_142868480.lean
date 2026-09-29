-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_149422080_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:31:08.409104+00:00
-- url     : https://prove2.me/submissions/8016a389-272e-47f4-9106-d82a9395954f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 57/320]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 147456000 131072000 134021120 ⟨⟨77930073601, 77930073608⟩, ⟨75395596267, 80490381421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 147456000 148111360 131072000 134021120 ⟨⟨77588724519, 77588724528⟩, ⟨75063600046, 80139516247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 147456000 134021120 136970240 ⟨⟨79540729065, 79540729073⟩, ⟨77000127222, 82107114272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 147456000 148111360 134021120 136970240 ⟨⟨79193247160, 79193247167⟩, ⟨76662011803, 81750103735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 148111360 148766720 131072000 134021120 ⟨⟨77249222273, 77249222279⟩, ⟨74733382419, 79790567781⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 148766720 149422080 131072000 134021120 ⟨⟨76911548032, 76911548037⟩, ⟨74404925333, 79443516397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 148111360 148766720 134021120 136970240 ⟨⟨78847635051, 78847635058⟩, ⟨76325698040, 81395032749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 148766720 149422080 134021120 136970240 ⟨⟨78503873755, 78503873759⟩, ⟨75991167722, 81041881535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 147456000 136970240 139919360 ⟨⟨81146752118, 81146752124⟩, ⟨78600068224, 83719172059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 147456000 148111360 136970240 139919360 ⟨⟨80793188758, 80793188764⟩, ⟨78255884380, 83356068122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 147456000 139919360 142868480 ⟨⟨82748183380, 82748183387⟩, ⟨80195459371, 85326595932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 147456000 148111360 139919360 142868480 ⟨⟨82388589288, 82388589296⟩, ⟨79845257241, 84957449903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 148111360 148766720 136970240 139919360 ⟨⟨80441517585, 80441517591⟩, ⟨77913524691, 82994926001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 148766720 149422080 136970240 139919360 ⟨⟨80091719468, 80091719469⟩, ⟨77572970795, 82635725768⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 148111360 148766720 139919360 142868480 ⟨⟨82030909216, 82030909224⟩, ⟨79496901217, 84590287387⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 148766720 149422080 139919360 142868480 ⟨⟨81675123891, 81675123896⟩, ⟨79150372785, 84225088320⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 149422080 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 148111360) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 147456000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 147456000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 148766720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 148766720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 148111360) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 147456000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 147456000) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 148766720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 148766720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (57/320 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
