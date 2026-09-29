-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u191365120_193986560_r148111360_153681920
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:40:47.112522+00:00
-- url     : https://prove2.me/submissions/eb1cddd9-3be7-4199-9b98-2a259e41cca4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [73/320, 37/160]`, `ρ ∈ [113/640, 469/2560]` by 14 cells of the computing
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
theorem cell0 : cellOK 191365120 192020480 148111360 149504000 ⟨⟨64955412799, 64955412802⟩, ⟨63291766856, 66630336888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 191365120 192020480 149504000 150896640 ⟨⟨65535186023, 65535186026⟩, ⟨63869421304, 67212230903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 192020480 192675840 148111360 149504000 ⟨⟨64680055626, 64680055633⟩, ⟨63020664627, 66350676274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 192020480 192675840 149504000 150896640 ⟨⟨65257584985, 65257584992⟩, ⟨63596080551, 66930321169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 191365120 192020480 150896640 153681920 ⟨⟨66403975280, 66403975283⟩, ⟨64388209724, 68436588139⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 192020480 192675840 150896640 153681920 ⟨⟨66123018320, 66123018326⟩, ⟨64113187939, 68149614204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 192675840 193331200 148111360 149504000 ⟨⟨64405756218, 64405756224⟩, ⟨62750595082, 66072098878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 192675840 193331200 149504000 150896640 ⟨⟨64981047924, 64981047930⟩, ⟨63323778694, 66649500865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193331200 193986560 148111360 149504000 ⟨⟨64132505764, 64132505770⟩, ⟨62481549638, 65794595665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 193331200 193986560 149504000 150896640 ⟨⟨64705565989, 64705565996⟩, ⟨63052507106, 66369760921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 192675840 193331200 150896640 152289280 ⟨⟨65555885571, 65555885577⟩, ⟨63896510503, 67226446511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 192675840 193331200 152289280 153681920 ⟨⟨66130270539, 66130270545⟩, ⟨64468791885, 67802937202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193331200 193986560 150896640 152289280 ⟨⟨65278177321, 65278177327⟩, ⟨63623017898, 66944475038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193331200 193986560 152289280 153681920 ⟨⟨65850341115, 65850341121⟩, ⟨64193083364, 67518739383⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 191365120 193986560 148111360 153681920 t = true :=
  ⟨_, (join_su (m := 192675840) (by decide) (join_sr (m := 150896640) (by decide) (join_su (m := 192020480) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 149504000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 192020480) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 150896640) (by decide) (join_su (m := 193331200) (by decide) (join_sr (m := 149504000) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 149504000) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 193331200) (by decide) (join_sr (m := 152289280) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 152289280) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (73/320 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  have e3 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
