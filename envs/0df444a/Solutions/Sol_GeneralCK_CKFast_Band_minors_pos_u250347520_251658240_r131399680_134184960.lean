-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u250347520_251658240_r131399680_134184960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:50:44.855604+00:00
-- url     : https://prove2.me/submissions/7aee2bc0-4619-4fc5-883b-b0a4aa27afb6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [191/640, 3/10]`, `ρ ∈ [401/2560, 819/5120]` by 13 cells of the computing
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
theorem cell0 : cellOK 250347520 250675200 131399680 132096000 ⟨⟨38713865968, 38713865974⟩, ⟨38042583649, 39387148882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 250347520 250675200 132096000 132792320 ⟨⟨38914421692, 38914421697⟩, ⟨38242721710, 39588123047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 250675200 251002880 131399680 132096000 ⟨⟨38621369081, 38621369087⟩, ⟨37950739551, 39293995954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 250675200 251002880 132096000 132792320 ⟨⟨38821463881, 38821463887⟩, ⟨38150417284, 39494508599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 250347520 250675200 132792320 134184960 ⟨⟨39215180814, 39215180820⟩, ⟨38431956940, 40001242607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 250675200 251002880 132792320 134184960 ⟨⟨39121532122, 39121532127⟩, ⟨38339249565, 39906647058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 251002880 251330560 131399680 132096000 ⟨⟨38528992675, 38528992681⟩, ⟨37859014394, 39200965059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251002880 251330560 132096000 132792320 ⟨⟨38728627029, 38728627035⟩, ⟨38058232279, 39401016662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 251330560 251658240 131399680 132096000 ⟨⟨38436736298, 38436736302⟩, ⟨37767407737, 39108055730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 251330560 251658240 132096000 132792320 ⟨⟨38635910684, 38635910687⟩, ⟨37966166250, 39307646771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251002880 251330560 132792320 134184960 ⟨⟨39028005103, 39028005108⟩, ⟨38246661842, 39812175227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251330560 251658240 132792320 133488640 ⟨⟨38835046151, 38835046154⟩, ⟨38164885864, 39507198871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 251330560 251658240 133488640 134184960 ⟨⟨39034142743, 39034142744⟩, ⟨38363566622, 39706712077⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 250347520 251658240 131399680 134184960 t = true :=
  ⟨_, (join_su (m := 251002880) (by decide) (join_sr (m := 132792320) (by decide) (join_su (m := 250675200) (by decide) (join_sr (m := 132096000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 132096000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 250675200) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 132792320) (by decide) (join_su (m := 251330560) (by decide) (join_sr (m := 132096000) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 132096000) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 251330560) (by decide) (leaf_ok cell10) (join_sr (m := 133488640) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (191/640 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (819/5120 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((134184960 : ℤ) : ℝ) / (D : ℝ)) = (819/5120 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
