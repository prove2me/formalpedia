-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u193986560_199229440_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:33:22.509591+00:00
-- url     : https://prove2.me/submissions/06fe4a49-af46-4cb9-b981-d4ce3a407d4a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [37/160, 19/80]`, `ρ ∈ [413/1280, 43/128]` by 15 cells of the computing
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
theorem cell0 : cellOK 193986560 195297280 270663680 273448960 ⟨⟨112575254790, 112575254798⟩, ⟨108941470240, 116253776948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 193986560 195297280 273448960 276234240 ⟨⟨113645657882, 113645657889⟩, ⟨110004161841, 117331894404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 195297280 196608000 270663680 273448960 ⟨⟨111677886212, 111677886220⟩, ⟨108061918783, 115338281682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 195297280 196608000 273448960 276234240 ⟨⟨112740940926, 112740940932⟩, ⟨109117282663, 116409031671⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 195297280 276234240 281804800 ⟨⟨115248733120, 115248733126⟩, ⟨110887719253, 119674943186⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 195297280 196608000 276234240 279019520 ⟨⟨113802673414, 113802673422⟩, ⟨110171336655, 117478446759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 195297280 196608000 279019520 281804800 ⟨⟨114863091515, 114863091522⟩, ⟨111224088512, 118546534864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 196608000 197918720 270663680 273448960 ⟨⟨110786012937, 110786012944⟩, ⟨107187681319, 114428466944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 196608000 197918720 273448960 276234240 ⟨⟨111841738924, 111841738931⟩, ⟨108235737535, 115491868672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 197918720 199229440 270663680 273448960 ⟨⟨109899554992, 109899555000⟩, ⟨106318680669, 113524249908⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 197918720 199229440 273448960 276234240 ⟨⟨110947971825, 110947971831⟩, ⟨107359449181, 114580322516⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 196608000 197918720 276234240 279019520 ⟨⟨112896170336, 112896170343⟩, ⟨109282511110, 116553963554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 196608000 197918720 279019520 281804800 ⟨⟨113949314795, 113949314803⟩, ⟨110328009590, 117614759288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 197918720 199229440 276234240 279019520 ⟨⟨111995121253, 111995121260⟩, ⟨108398961832, 115635115846⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 197918720 199229440 279019520 281804800 ⟨⟨113041010691, 113041010699⟩, ⟨109437225961, 116688637388⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 193986560 199229440 270663680 281804800 t = true :=
  ⟨_, (join_su (m := 196608000) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 195297280) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 273448960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 195297280) (by decide) (leaf_ok cell4) (join_sr (m := 279019520) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 276234240) (by decide) (join_su (m := 197918720) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 273448960) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 197918720) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 279019520) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (37/160 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
