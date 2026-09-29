-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_196608000_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:27:41.806116+00:00
-- url     : https://prove2.me/submissions/69a13a00-6fbd-4cd8-aeef-198483460998

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 15/64]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 193986560 194641920 131399680 132792320 ⟨⟨56975169170, 56975169177⟩, ⟨55353735232, 58607659336⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 193986560 194641920 132792320 134184960 ⟨⟨57551435354, 57551435362⟩, ⟨55927877256, 59186052333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 194641920 195297280 131399680 132792320 ⟨⟨56731023720, 56731023721⟩, ⟨55113678728, 58359376967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 194641920 195297280 132792320 134184960 ⟨⟨57305008319, 57305008322⟩, ⟨55685544970, 58935482654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 194641920 134184960 135577600 ⟨⟨58127241364, 58127241370⟩, ⟨56501561372, 59763982859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193986560 194641920 135577600 136970240 ⟨⟨58702588588, 58702588593⟩, ⟨57074788967, 60341452313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 194641920 195297280 134184960 135577600 ⟨⟨57878538054, 57878538057⟩, ⟨56256958577, 59511131223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 194641920 195297280 135577600 136970240 ⟨⟨58451614295, 58451614298⟩, ⟨56827920911, 60086324050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 195297280 195952640 131399680 132792320 ⟨⟨56487824492, 56487824499⟩, ⟨54874544333, 58112065323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 195297280 195952640 132792320 134184960 ⟨⟨57059534211, 57059534217⟩, ⟨55444141489, 58685890412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 195952640 196608000 131399680 132792320 ⟨⟨56245563544, 56245563551⟩, ⟨54636324314, 57865716236⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 195952640 196608000 132792320 134184960 ⟨⟨56815005040, 56815005047⟩, ⟨55203659033, 58437267393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 195297280 195952640 134184960 135577600 ⟨⟨57630794321, 57630794328⟩, ⟨56013291226, 59259263679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 195297280 195952640 135577600 136970240 ⟨⟨58201606172, 58201606178⟩, ⟨56581994884, 59832186480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 195952640 196608000 134184960 135577600 ⟨⟨57384002129, 57384002136⟩, ⟨55770551493, 59008371970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 195952640 196608000 135577600 136970240 ⟨⟨57952556139, 57952556145⟩, ⟨56337003016, 59579031301⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 196608000 131399680 136970240 t = true :=
  ⟨_, (join_su (m := 195297280) (by decide) (join_sr (m := 134184960) (by decide) (join_su (m := 194641920) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 132792320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 194641920) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 135577600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 134184960) (by decide) (join_su (m := 195952640) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 132792320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 195952640) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 135577600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (15/64 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
