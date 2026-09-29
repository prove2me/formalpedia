-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_196608000_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:41:11.269382+00:00
-- url     : https://prove2.me/submissions/f830adcd-ab0a-4326-a0db-50bad411dc84

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 15/64]`, `ρ ∈ [469/2560, 243/1280]` by 10 cells of the computing
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
theorem cell0 : cellOK 193986560 194641920 153681920 156467200 ⟨⟨66425566477, 66425566484⟩, ⟨64428724569, 68438930585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 194641920 195297280 153681920 156467200 ⟨⟨66144440958, 66144440961⟩, ⟨64153415772, 68151909337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 194641920 156467200 159252480 ⟨⟨67562825384, 67562825391⟩, ⟨65561376135, 69580795031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 194641920 195297280 156467200 159252480 ⟨⟨67277311543, 67277311546⟩, ⟨65281691437, 69289373337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 195297280 195952640 153681920 155074560 ⟨⟨65581974049, 65581974056⟩, ⟨63935151543, 67239799233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 195297280 195952640 155074560 156467200 ⟨⟨66146649382, 66146649387⟩, ⟨64497748477, 67806555384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195952640 196608000 153681920 155074560 ⟨⟨65304034116, 65304034124⟩, ⟨63661340450, 66957684500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 195952640 196608000 155074560 156467200 ⟨⟨65866521984, 65866521990⟩, ⟨64221755092, 67522248091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 195297280 195952640 156467200 159252480 ⟨⟨66992859235, 66992859241⟩, ⟨65003036229, 68999045827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 195952640 196608000 156467200 159252480 ⟨⟨66709459778, 66709459784⟩, ⟨64725402107, 68709803525⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 196608000 153681920 159252480 t = true :=
  ⟨_, (join_su (m := 195297280) (by decide) (join_sr (m := 156467200) (by decide) (join_su (m := 194641920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 194641920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 156467200) (by decide) (join_su (m := 195952640) (by decide) (join_sr (m := 155074560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 155074560) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 195952640) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (15/64 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
