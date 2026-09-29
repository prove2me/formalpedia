-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r198246400_203816960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:23:31.795971+00:00
-- url     : https://prove2.me/submissions/29a0b8aa-fa97-4cb6-a44d-a9e03bc48a1e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [121/512, 311/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 198246400 199639040 ⟨⟨58367245809, 58367245815⟩, ⟨56941376866, 59801453136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249036800 249692160 199639040 201031680 ⟨⟨58764110231, 58764110237⟩, ⟨57336572873, 60199991791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249692160 250347520 198246400 199639040 ⟨⟨58094698107, 58094698113⟩, ⟨56671669638, 59526039722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 199639040 201031680 ⟨⟨58489812330, 58489812335⟩, ⟨57065119653, 59922823997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 249692160 201031680 202424320 ⟨⟨59160828854, 59160828860⟩, ⟨57731623256, 60598384462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 249036800 249692160 202424320 203816960 ⟨⟨59557402008, 59557402015⟩, ⟨58126528345, 60996631485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250347520 201031680 202424320 ⟨⟨58884782663, 58884782670⟩, ⟨57458425941, 60319464211⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249692160 250347520 202424320 203816960 ⟨⟨59279609435, 59279609440⟩, ⟨57851588827, 60715960691⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 251002880 198246400 199639040 ⟨⟨57822797314, 57822797316⟩, ⟨56402596584, 59251286102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250347520 251002880 199639040 201031680 ⟨⟨58216164144, 58216164146⟩, ⟨56794303407, 59646318805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251002880 251658240 198246400 199639040 ⟨⟨57551538780, 57551538786⟩, ⟨56134153142, 58977187544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251002880 251658240 199639040 201031680 ⟨⟨57943161008, 57943161014⟩, ⟨56524119562, 59370471471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 201031680 202424320 ⟨⟨58609388976, 58609388978⟩, ⟨57185868384, 60041209351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251002880 202424320 203816960 ⟨⟨59002472129, 59002472132⟩, ⟨57577291831, 60435958061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251658240 201031680 202424320 ⟨⟨58334643108, 58334643115⟩, ⟨56913945994, 59763615123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 202424320 203816960 ⟨⟨58725985397, 58725985402⟩, ⟨57303632753, 60156618814⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 198246400 203816960 t = true :=
  ⟨_, (join_su (m := 250347520) (by decide) (join_sr (m := 201031680) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 199639040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 249692160) (by decide) (join_sr (m := 202424320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202424320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 201031680) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 199639040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 199639040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 251002880) (by decide) (join_sr (m := 202424320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 202424320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (121/512 : ℝ) (311/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((198246400 : ℤ) : ℝ) / (D : ℝ)) = (121/512 : ℝ) := by norm_num [D]
  have e3 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
