-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r281804800_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:33:34.015503+00:00
-- url     : https://prove2.me/submissions/a7f28a20-336d-4a73-856c-6474b517b1de

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [43/128, 29/80]` by 17 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 281804800 287375360 ⟨⟨117381487379, 117381487385⟩, ⟨113003827396, 121824290646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 195297280 196608000 281804800 287375360 ⟨⟨116451271214, 116451271222⟩, ⟨112098234853, 120868939346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 193986560 195297280 287375360 292945920 ⟨⟨119508952099, 119508952105⟩, ⟨115114711872, 123968281063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 287375360 292945920 ⟨⟨118564316125, 118564316133⟩, ⟨114194742597, 122998472106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 196608000 197918720 281804800 287375360 ⟨⟨115526635013, 115526635021⟩, ⟨111197985820, 119919410690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 197918720 199229440 281804800 284590080 ⟨⟨114085647515, 114085647522⟩, ⟨110474248868, 117740894592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 197918720 199229440 284590080 287375360 ⟨⟨115129039057, 115129039063⟩, ⟨111510037811, 118791894864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 196608000 197918720 287375360 292945920 ⟨⟨117625294688, 117625294696⟩, ⟨113280152567, 122034519072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 197918720 199229440 287375360 292945920 ⟨⟨116691807407, 116691807415⟩, ⟨112370864945, 121076337937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 193986560 195297280 292945920 298516480 ⟨⟨121631190246, 121631190252⟩, ⟨117220434720, 126106978346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 195297280 196608000 292945920 298516480 ⟨⟨120672242287, 120672242295⟩, ⟨116286194611, 125122821498⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 193986560 195297280 298516480 304087040 ⟨⟨123748264080, 123748264087⟩, ⟨119321057279, 128240445679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 195297280 196608000 298516480 304087040 ⟨⟨122775110298, 122775110307⟩, ⟨118372650609, 127242049010⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 197918720 292945920 298516480 ⟨⟨119718941618, 119718941626⟩, ⟨115357367693, 124144551997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 199229440 292945920 298516480 ⟨⟨118771207795, 118771207802⟩, ⟨114433877027, 123172085799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 197918720 298516480 304087040 ⟨⟨121807634786, 121807634793⟩, ⟨117429689334, 126249569303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 197918720 199229440 298516480 304087040 ⟨⟨120845757052, 120845757060⟩, ⟨116492096430, 125262922517⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 281804800 304087040 t = true :=
  ⟨_, (join_sr (m := 292945920) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 287375360) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 195297280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 287375360) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell4) (join_sr (m := 284590080) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 197918720) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 196608000) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 195297280) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 195297280) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 298516480) (by decide) (join_su (m := 197918720) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 197918720) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (43/128 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
