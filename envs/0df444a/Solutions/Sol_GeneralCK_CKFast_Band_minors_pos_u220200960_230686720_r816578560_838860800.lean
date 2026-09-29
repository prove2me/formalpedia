-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_230686720_r816578560_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:15:29.550273+00:00
-- url     : https://prove2.me/submissions/57821ec5-0b66-4281-af92-0221d3500ff6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 11/40]`, `ρ ∈ [623/640, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 222822400 816578560 822149120 ⟨⟨264827085405, 264827085415⟩, ⟨255574883898, 274238036973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 222822400 822149120 827719680 ⟨⟨266473164135, 266473164145⟩, ⟨257194428209, 275910450283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 225443840 816578560 822149120 ⟨⟨261000265976, 261000265987⟩, ⟨251812577945, 270346830081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 222822400 225443840 822149120 827719680 ⟨⟨262626815817, 262626815826⟩, ⟨253412563232, 271999771107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 222822400 827719680 833290240 ⟨⟨268118355867, 268118355876⟩, ⟨258813089413, 277581967533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 222822400 833290240 838860800 ⟨⟨269762679988, 269762679998⟩, ⟨260430886539, 279252608444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 222822400 225443840 827719680 833290240 ⟨⟨264252510972, 264252510982⟩, ⟨255011696470, 273651849760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 225443840 833290240 838860800 ⟨⟨265877370053, 265877370063⟩, ⟨256609995927, 275303084964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 225443840 228065280 816578560 822149120 ⟨⟨257187497760, 257187497769⟩, ⟨248064009240, 266469964090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 225443840 228065280 822149120 827719680 ⟨⟨258794411522, 258794411531⟩, ⟨249644338021, 268103315371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 230686720 816578560 822149120 ⟨⟨253388494374, 253388494378⟩, ⟨244328895220, 262607149423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228065280 230686720 822149120 827719680 ⟨⟨254975667523, 254975667526⟩, ⟨245889472474, 264220796340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 225443840 228065280 827719680 833290240 ⟨⟨260400502249, 260400502259⟩, ⟨251223845159, 269735837290⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 225443840 228065280 833290240 838860800 ⟨⟨262005787796, 262005787805⟩, ⟨252802548182, 271367547996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 228065280 230686720 827719680 833290240 ⟨⟨256562048616, 256562048622⟩, ⟨247449257840, 265833646221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 228065280 230686720 833290240 838860800 ⟨⟨258147654773, 258147654778⟩, ⟨249008268123, 267445716467⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 230686720 816578560 838860800 t = true :=
  ⟨_, (join_su (m := 225443840) (by decide) (join_sr (m := 827719680) (by decide) (join_su (m := 222822400) (by decide) (join_sr (m := 822149120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 822149120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 222822400) (by decide) (join_sr (m := 833290240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 833290240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 827719680) (by decide) (join_su (m := 228065280) (by decide) (join_sr (m := 822149120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 822149120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 228065280) (by decide) (join_sr (m := 833290240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 833290240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (623/640 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e2 : (((816578560 : ℤ) : ℝ) / (D : ℝ)) = (623/640 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
