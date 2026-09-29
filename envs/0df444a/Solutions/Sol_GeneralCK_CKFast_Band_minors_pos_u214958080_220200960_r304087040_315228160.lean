-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r304087040_315228160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:00:47.831849+00:00
-- url     : https://prove2.me/submissions/fcd0d109-08f6-401f-ba1b-6c1b0b9ffc4d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [29/80, 481/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 304087040 306872320 ⟨⟨110234183374, 110234183380⟩, ⟨106777561231, 113731291335⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 214958080 216268800 306872320 309657600 ⟨⟨111178201853, 111178201859⟩, ⟨107714321980, 114682587976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 216268800 217579520 304087040 306872320 ⟨⟨109332694869, 109332694877⟩, ⟨105891582667, 112814051463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 306872320 309657600 ⟨⟨110269913275, 110269913281⟩, ⟨106821565497, 113758526963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 216268800 309657600 312442880 ⟨⟨112121326265, 112121326271⟩, ⟨108650195243, 115632983705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214958080 216268800 312442880 315228160 ⟨⟨113063561490, 113063561496⟩, ⟨109585185858, 116582483444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 217579520 309657600 312442880 ⟨⟨111206257156, 111206257162⟩, ⟨107750680105, 114702121379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216268800 217579520 312442880 315228160 ⟨⟨112141731260, 112141731268⟩, ⟨108678931204, 115644839492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218890240 304087040 306872320 ⟨⟨108435765308, 108435765315⟩, ⟨105010023357, 111901512913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217579520 218890240 306872320 309657600 ⟨⟨109366197371, 109366197378⟩, ⟨105933242284, 112839180691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 220200960 304087040 306872320 ⟨⟨107543332577, 107543332580⟩, ⟨104132823110, 110993611603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218890240 220200960 306872320 309657600 ⟨⟨108466991978, 108466991981⟩, ⟨105049292096, 111924485034⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 309657600 312442880 ⟨⟨110295774117, 110295774125⟩, ⟨106855611930, 113775986867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 217579520 218890240 312442880 315228160 ⟨⟨111224500166, 111224500173⟩, ⟨107777136872, 114711936092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 220200960 309657600 312442880 ⟨⟨109389814938, 109389814941⟩, ⟨105964930408, 112854516009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218890240 220200960 312442880 315228160 ⟨⟨110311805948, 110311805952⟩, ⟨106879742503, 113783709049⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 304087040 315228160 t = true :=
  ⟨_, (join_su (m := 217579520) (by decide) (join_sr (m := 309657600) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 306872320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 216268800) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 312442880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 309657600) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 306872320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 306872320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 218890240) (by decide) (join_sr (m := 312442880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 312442880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (29/80 : ℝ) (481/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  have e3 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
