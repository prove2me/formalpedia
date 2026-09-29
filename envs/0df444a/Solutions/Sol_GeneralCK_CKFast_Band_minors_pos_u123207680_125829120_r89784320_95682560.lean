-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u123207680_125829120_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:18:50.028283+00:00
-- url     : https://prove2.me/submissions/e382193c-3db1-445a-bdc8-fa7b5c28823f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/320, 3/20]`, `ρ ∈ [137/1280, 73/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 123207680 123863040 89784320 91258880 ⟨⟨64497109195, 64497109202⟩, ⟨62276125710, 66739270805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 123207680 123863040 91258880 92733440 ⟨⟨65475850297, 65475850306⟩, ⟨63251548179, 67721307185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 123863040 124518400 89784320 91258880 ⟨⟨64184145223, 64184145230⟩, ⟨61972053012, 66417259681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 123863040 124518400 91258880 92733440 ⟨⟨65158712563, 65158712572⟩, ⟨62943311350, 67395113262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 123207680 123863040 92733440 94208000 ⟨⟨66452557783, 66452557792⟩, ⟨64224953735, 68701293177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 123207680 123863040 94208000 95682560 ⟨⟨67427242936, 67427242945⟩, ⟨65196353525, 69679240201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 123863040 124518400 92733440 94208000 ⟨⟨66131270861, 66131270868⟩, ⟨63912577091, 68370941287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 123863040 124518400 94208000 95682560 ⟨⟨67101831200, 67101831207⟩, ⟨64879861189, 69344754966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 124518400 125173760 89784320 91258880 ⟨⟨63873391030, 63873391037⟩, ⟨61670108511, 66097541857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 124518400 125173760 91258880 92733440 ⟨⟨64843807209, 64843807218⟩, ⟨62637225344, 67071235199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125173760 125829120 89784320 91258880 ⟨⟨63564819084, 63564819091⟩, ⟨61370265805, 65780088627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 125173760 125829120 91258880 92733440 ⟨⟨64531106488, 64531106495⟩, ⟨62333263549, 66749644077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 124518400 125173760 92733440 94208000 ⟨⟨65812238594, 65812238601⟩, ⟨63602373579, 68042927481⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 124518400 125173760 94208000 95682560 ⟨⟨66778696071, 66778696078⟩, ⟨64565563972, 69012629724⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 125173760 125829120 92733440 94208000 ⟨⟨65495433026, 65495433035⟩, ⟨63294316376, 67717222647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 125173760 125829120 94208000 95682560 ⟨⟨66457809395, 66457809403⟩, ⟨64253434853, 68682835154⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 123207680 125829120 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 124518400) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 123863040) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 91258880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 123863040) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 94208000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 92733440) (by decide) (join_su (m := 125173760) (by decide) (join_sr (m := 91258880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 91258880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 125173760) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 94208000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/320 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((123207680 : ℤ) : ℝ) / (D : ℝ)) = (47/320 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
