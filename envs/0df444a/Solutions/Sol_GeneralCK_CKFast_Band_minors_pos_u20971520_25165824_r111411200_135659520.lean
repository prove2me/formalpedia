-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r111411200_135659520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:26:09.161958+00:00
-- url     : https://prove2.me/submissions/ff218fef-2f9c-4c41-a38f-fe748d036579

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/40, 3/100]`, `ρ ∈ [17/128, 207/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 20971520 22020096 111411200 117473280 ⟨⟨226284658039, 226284658063⟩, ⟨209385409432, 243995045080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 22020096 23068672 111411200 117473280 ⟨⟨222259054493, 222259054518⟩, ⟨205757120916, 239542245016⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 20971520 22020096 117473280 123535360 ⟨⟨233445737910, 233445737930⟩, ⟨216722187678, 250939867559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 22020096 23068672 117473280 123535360 ⟨⟨229404767448, 229404767468⟩, ⟨213064436482, 246488341159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 23068672 24117248 111411200 117473280 ⟨⟨218384718965, 218384718989⟩, ⟨202261393498, 235261077826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 24117248 25165824 111411200 117473280 ⟨⟨214652423633, 214652423657⟩, ⟨198890320949, 231140874009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 23068672 24117248 117473280 123535360 ⟨⟨225511624548, 225511624572⟩, ⟨209536916436, 242203696563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 24117248 25165824 117473280 123535360 ⟨⟨221757478078, 221757478101⟩, ⟨206132014712, 238075783300⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 20971520 22020096 123535360 129597440 ⟨⟨240379270284, 240379270310⟩, ⟨223828917034, 257662399529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 22020096 23068672 123535360 129597440 ⟨⟨236327243852, 236327243871⟩, ⟨220146693965, 253215530583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 20971520 22020096 129597440 135659520 ⟨⟨247101406764, 247101406785⟩, ⟨230721456626, 264178843410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 22020096 23068672 129597440 135659520 ⟨⟨243042043976, 243042043995⟩, ⟨227019129707, 259739484273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 23068672 24117248 123535360 129597440 ⟨⟨232419645266, 232419645286⟩, ⟨216592327393, 248930943889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 24117248 25165824 123535360 129597440 ⟨⟨228648017033, 228648017052⟩, ⟨213158485389, 244798971439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 23068672 24117248 129597440 135659520 ⟨⟨239123766310, 239123766334⟩, ⟨223442263575, 255457964566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 24117248 25165824 129597440 135659520 ⟨⟨235338467852, 235338467871⟩, ⟨219983794474, 251325064933⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 20971520 25165824 111411200 135659520 t = true :=
  ⟨_, (join_sr (m := 123535360) (by decide) (join_su (m := 23068672) (by decide) (join_sr (m := 117473280) (by decide) (join_su (m := 22020096) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 22020096) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 117473280) (by decide) (join_su (m := 24117248) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 24117248) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 23068672) (by decide) (join_sr (m := 129597440) (by decide) (join_su (m := 22020096) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 22020096) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 129597440) (by decide) (join_su (m := 24117248) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 24117248) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/40 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((20971520 : ℤ) : ℝ) / (D : ℝ)) = (1/40 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((111411200 : ℤ) : ℝ) / (D : ℝ)) = (17/128 : ℝ) := by norm_num [D]
  have e3 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
