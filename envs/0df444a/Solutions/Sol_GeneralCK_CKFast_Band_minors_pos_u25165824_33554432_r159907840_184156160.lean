-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r159907840_184156160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:28:06.713406+00:00
-- url     : https://prove2.me/submissions/fb89fea8-1529-4113-9994-842d1035763f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 1/25]`, `ρ ∈ [61/320, 281/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 25165824 27262976 159907840 165969920 ⟨⟨260702092049, 260702092062⟩, ⟨239965652132, 282500740059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 25165824 27262976 165969920 172032000 ⟨⟨266427355694, 266427355707⟩, ⟨245831556790, 288045126816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 27262976 29360128 159907840 165969920 ⟨⟨253721879499, 253721879520⟩, ⟨233699632274, 274753890304⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 27262976 29360128 165969920 172032000 ⟨⟨259436131988, 259436132006⟩, ⟨239535656644, 280309851157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 25165824 27262976 172032000 178094080 ⟨⟨272025984732, 272025984746⟩, ⟨251569097999, 293466619460⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 25165824 27262976 178094080 184156160 ⟨⟨277504825097, 277504825111⟩, ⟨257185005964, 298772046074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 27262976 29360128 172032000 178094080 ⟨⟨265027082491, 265027082508⟩, ⟨245247345723, 285745282480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 27262976 29360128 178094080 184156160 ⟨⟨270501215924, 270501215945⟩, ⟨250841041833, 291066701988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 29360128 31457280 159907840 165969920 ⟨⟨247120728120, 247120728141⟩, ⟨227762647629, 267439916511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 29360128 31457280 165969920 172032000 ⟨⟨252816919239, 252816919260⟩, ⟨233563928280, 272997797809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 31457280 33554432 159907840 165969920 ⟨⟨240864706254, 240864706273⟩, ⟨222126074253, 260519258679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 31457280 33554432 165969920 172032000 ⟨⟨246536900624, 246536900644⟩, ⟨227888568278, 266070871680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 29360128 31457280 172032000 178094080 ⟨⟨258393259647, 258393259667⟩, ⟨239244892468, 278437801370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 29360128 31457280 178094080 184156160 ⟨⟨263855883997, 263855884018⟩, ⟨244811514027, 283766132224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 31457280 33554432 172032000 178094080 ⟨⟨252092761241, 252092761257⟩, ⟨233534725139, 271507463475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 31457280 33554432 178094080 184156160 ⟨⟨257538085558, 257538085574⟩, ⟨239070169831, 276834929364⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 33554432 159907840 184156160 t = true :=
  ⟨_, (join_su (m := 29360128) (by decide) (join_sr (m := 172032000) (by decide) (join_su (m := 27262976) (by decide) (join_sr (m := 165969920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 165969920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 27262976) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 178094080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 172032000) (by decide) (join_su (m := 31457280) (by decide) (join_sr (m := 165969920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 165969920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 31457280) (by decide) (join_sr (m := 178094080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 178094080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e3 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
