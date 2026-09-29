-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u201850880_204472320_r136970240_142540800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:50:56.117846+00:00
-- url     : https://prove2.me/submissions/6a664129-c914-43d2-932c-83c37f9f552f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [77/320, 39/160]`, `ρ ∈ [209/1280, 87/512]` by 16 cells of the computing
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
theorem cell0 : cellOK 201850880 202506240 136970240 138362880 ⟨⟨56301050400, 56301050406⟩, ⟨54718928268, 57893691302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 202506240 138362880 139755520 ⟨⟨56848777310, 56848777316⟩, ⟨55264607225, 58443469591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 202506240 203161600 136970240 138362880 ⟨⟨56058964636, 56058964643⟩, ⟨54480678184, 57647726456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 202506240 203161600 138362880 139755520 ⟨⟨56604506143, 56604506149⟩, ⟨55024177279, 58195313867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 201850880 202506240 139755520 141148160 ⟨⟨57396108832, 57396108839⟩, ⟨55809892589, 58992850679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201850880 202506240 141148160 142540800 ⟨⟨57943046108, 57943046115⟩, ⟨56354785493, 59541835707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 202506240 203161600 139755520 141148160 ⟨⟨57149656874, 57149656879⟩, ⟨55567287359, 58742508721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 202506240 203161600 141148160 142540800 ⟨⟨57694417951, 57694417957⟩, ⟨56110009537, 59289312145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 203161600 203816960 136970240 138362880 ⟨⟨55817759406, 55817759412⟩, ⟨54243286890, 57402664217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 203161600 203816960 138362880 139755520 ⟨⟨56361121502, 56361121508⟩, ⟨54784612107, 57948066750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203816960 204472320 136970240 138362880 ⟨⟨55577427523, 55577427530⟩, ⟨54006747387, 57158497212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 203816960 204472320 138362880 139755520 ⟨⟨56118616164, 56118616169⟩, ⟨54545904671, 57701720830⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 203161600 203816960 139755520 141148160 ⟨⟨56904097386, 56904097392⟩, ⟨55325552837, 58493081324⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203161600 203816960 141148160 142540800 ⟨⟨57446688162, 57446688169⟩, ⟨55866110179, 59037709047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203816960 204472320 139755520 141148160 ⟨⟨56659423109, 56659423115⟩, ⟨55084681950, 58244561039⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203816960 204472320 141148160 142540800 ⟨⟨57199849445, 57199849450⟩, ⟨55623080307, 58787018930⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 201850880 204472320 136970240 142540800 t = true :=
  ⟨_, (join_su (m := 203161600) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 202506240) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 138362880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 202506240) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 141148160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 139755520) (by decide) (join_su (m := 203816960) (by decide) (join_sr (m := 138362880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 138362880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 203816960) (by decide) (join_sr (m := 141148160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 141148160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (77/320 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (87/512 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
