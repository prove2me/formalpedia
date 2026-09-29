-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u107479040_110100480_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:03:41.012032+00:00
-- url     : https://prove2.me/submissions/5fddbaaa-7e0e-433e-bcab-9ac4592274dd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/320, 21/160]`, `ρ ∈ [137/1280, 73/640]` by 15 cells of the computing
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
theorem cell0 : cellOK 107479040 108134400 89784320 91258880 ⟨⟨72751928481, 72751928489⟩, ⟨70289696459, 75239759026⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 107479040 108134400 91258880 92733440 ⟨⟨73838213612, 73838213622⟩, ⟨71372448779, 76329534741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 108134400 108789760 89784320 91258880 ⟨⟨72376275012, 72376275019⟩, ⟨69925298464, 74852635801⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 108134400 108789760 91258880 92733440 ⟨⟨73457773946, 73457773956⟩, ⟨71003272499, 75937618410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 107479040 108134400 92733440 95682560 ⟨⟨75462516821, 75462516831⟩, ⟨72297829952, 78669180654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 108134400 108789760 92733440 94208000 ⟨⟨74536571087, 74536571095⟩, ⟨72078568573, 77019875338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 108134400 108789760 94208000 95682560 ⟨⟨75612683648, 75612683656⟩, ⟨73151203670, 78099424041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 108789760 109445120 89784320 91258880 ⟨⟨72003660551, 72003660559⟩, ⟨69563822709, 74468671334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 108789760 109445120 91258880 92733440 ⟨⟨73080401740, 73080401747⟩, ⟨70637047035, 75548889141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 109445120 110100480 89784320 91258880 ⟨⟨71634042812, 71634042814⟩, ⟨69205228743, 74087821448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 109445120 110100480 91258880 92733440 ⟨⟨72706054429, 72706054433⟩, ⟨70273731653, 75163302490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 108789760 109445120 92733440 94208000 ⟨⟨74154474841, 74154474851⟩, ⟨71707626741, 76626415346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 108789760 109445120 94208000 95682560 ⟨⟨75225896756, 75225896765⟩, ⟨72775578500, 77701267069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 109445120 110100480 92733440 94208000 ⟨⟨73775431195, 73775431201⟩, ⟨71339622816, 76236125524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 109445120 110100480 94208000 95682560 ⟨⟨74842189694, 74842189700⟩, ⟨72402918597, 77306307353⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 107479040 110100480 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 108789760) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 108134400) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 91258880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 108134400) (by decide) (leaf_ok cell4) (join_sr (m := 94208000) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 92733440) (by decide) (join_su (m := 109445120) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 91258880) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 109445120) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 94208000) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/320 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
