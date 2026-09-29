-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_193986560_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:23:34.419895+00:00
-- url     : https://prove2.me/submissions/4d7bbe05-9af3-4ee2-94f0-8f64e4a5f0b9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 37/160]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 190054400 214958080 217743360 ⟨⟨93898854154, 93898854160⟩, ⟨90350919929, 97492803106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 190054400 217743360 220528640 ⟨⟨95030179956, 95030179963⟩, ⟨91474144867, 98632233458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 190054400 191365120 214958080 217743360 ⟨⟨93133952522, 93133952528⟩, ⟨89604113657, 96709446423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 190054400 191365120 217743360 220528640 ⟨⟨94257193532, 94257193540⟩, ⟨90719282350, 97840765074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 190054400 220528640 223313920 ⟨⟨96159846156, 96159846163⟩, ⟨92595726808, 99769987217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 190054400 223313920 226099200 ⟨⟨97287862921, 97287862927⟩, ⟨93715675803, 100906074664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 190054400 191365120 220528640 223313920 ⟨⟨95378810388, 95378810396⟩, ⟨91832842965, 98970443113⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 190054400 191365120 223313920 226099200 ⟨⟨96498812970, 96498812976⟩, ⟨92944805274, 100098490527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 191365120 192675840 214958080 217743360 ⟨⟨92374363380, 92374363388⟩, ⟨88862419269, 95931607954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 191365120 192675840 217743360 220528640 ⟨⟨93489551268, 93489551275⟩, ⟨89969563667, 97054846242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 192675840 193986560 214958080 217743360 ⟨⟨91620004128, 91620004131⟩, ⟨88125757504, 95159201651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 192675840 193986560 217743360 220528640 ⟨⟨92727170296, 92727170298⟩, ⟨89224909279, 96274390666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 191365120 192675840 220528640 223313920 ⟨⟨94603149793, 94603149800⟩, ⟨91075134265, 98176479233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 191365120 192675840 223313920 226099200 ⟨⟨95715168554, 95715168562⟩, ⟨92179140555, 99296516630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 192675840 193986560 220528640 223313920 ⟨⟨93832781249, 93832781252⟩, ⟨90322520898, 97388009045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 192675840 193986560 223313920 226099200 ⟨⟨94936846315, 94936846320⟩, ⟨91418601586, 98500066213⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 193986560 214958080 226099200 t = true :=
  ⟨_, (join_su (m := 191365120) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 190054400) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 217743360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 190054400) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 223313920) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 192675840) (by decide) (join_sr (m := 217743360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 217743360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 192675840) (by decide) (join_sr (m := 223313920) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 223313920) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
