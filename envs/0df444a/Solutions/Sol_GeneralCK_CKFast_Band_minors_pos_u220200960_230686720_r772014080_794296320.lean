-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r772014080_794296320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:12:46.1269+00:00
-- url     : https://prove2.me/submissions/956a06c1-072c-43b7-9f3c-d2e6383d4306

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [589/640, 303/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 772014080 777584640 ⟨⟨251624172198, 251624172209⟩, ⟨242584429509, 260824080896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 777584640 783155200 ⟨⟨253278053972, 253278053981⟩, ⟨244211732716, 262504381766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 772014080 777584640 ⟨⟨247954842316, 247954842325⟩, ⟨238979806743, 257089962188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 777584640 783155200 ⟨⟨249588908046, 249588908055⟩, ⟨240587274486, 258750492007⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 783155200 788725760 ⟨⟨254930890891, 254930890901⟩, ⟨245837997856, 264183626040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 788725760 794296320 ⟨⟨256582702968, 256582702977⟩, ⟨247463244574, 265861834069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 783155200 788725760 ⟨⟨251221967648, 251221967657⟩, ⟨242193741482, 260410005476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 788725760 794296320 ⟨⟨252854040314, 252854040324⟩, ⟨243799226579, 262068522101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 772014080 777584640 ⟨⟨244300394547, 244300394556⟩, ⟨235389675044, 253371097045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 777584640 783155200 ⟨⟨245914543167, 245914543176⟩, ⟨236977215830, 255011744578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 230686720 772014080 777584640 ⟨⟨240660521197, 240660521202⟩, ⟨231813732104, 249667172954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228065280 230686720 777584640 783155200 ⟨⟨242254654314, 242254654319⟩, ⟨233381256914, 251287829847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 225443840 228065280 783155200 788725760 ⟨⟨247527723541, 247527723551⟩, ⟨238563792368, 256651415141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 228065280 788725760 794296320 ⟨⟨249139954064, 249139954073⟩, ⟨240149422722, 258290127429⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 230686720 783155200 788725760 ⟨⟨243847856218, 243847856223⟩, ⟨234947853143, 252907548285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 230686720 788725760 794296320 ⟨⟨245440144533, 245440144538⟩, ⟨236513538104, 254526346174⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 772014080 794296320 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 783155200) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 777584640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 777584640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 788725760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 788725760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 783155200) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 777584640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 777584640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 228065280) (by decide) (join_sr (m := 788725760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 788725760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (589/640 : ℝ) (303/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((772014080 : ℤ) : ℝ) / (D : ℝ)) = (589/640 : ℝ) := by norm_num [D]
  have e3 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
