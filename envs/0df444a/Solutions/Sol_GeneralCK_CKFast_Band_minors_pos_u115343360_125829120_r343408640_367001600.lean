-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_125829120_r343408640_367001600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:43:41.218036+00:00
-- url     : https://prove2.me/submissions/8975f6b5-5330-49e7-a564-5bd2f61c3d3a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 3/20]`, `ρ ∈ [131/320, 7/16]` by 16 cells of the computing
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
theorem cell0 : cellOK 115343360 117964800 343408640 349306880 ⟨⟨219754165724, 219754165735⟩, ⟨208980577578, 230806010527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 117964800 349306880 355205120 ⟨⟨222802413294, 222802413305⟩, ⟨212002886643, 233878187339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 117964800 120586240 343408640 349306880 ⟨⟨216469711583, 216469711594⟩, ⟨205837213976, 227376008067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 117964800 120586240 349306880 355205120 ⟨⟨219489766252, 219489766263⟩, ⟨208830672453, 230420770798⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 117964800 355205120 361103360 ⟨⟨225835857578, 225835857589⟩, ⟨215010714654, 236935242944⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 115343360 117964800 361103360 367001600 ⟨⟨228854774767, 228854774779⟩, ⟨218004328980, 239977462373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 117964800 120586240 355205120 361103360 ⟨⟨222495482792, 222495482803⟩, ⟨211810107876, 233450883207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 117964800 120586240 361103360 367001600 ⟨⟨225487124893, 225487124904⟩, ⟨214775775544, 236466617407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 120586240 123207680 343408640 349306880 ⟨⟨213243046537, 213243046547⟩, ⟨202748031303, 224007516966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 120586240 123207680 349306880 355205120 ⟨⟨216234763523, 216234763534⟩, ⟨205712547572, 227024661660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 123207680 125829120 343408640 349306880 ⟨⟨210072160227, 210072160234⟩, ⟨199711158577, 220698384035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 123207680 125829120 349306880 355205120 ⟨⟨213035413441, 213035413444⟩, ⟨202646656488, 223687728980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 120586240 123207680 355205120 361103360 ⟨⟨219212596484, 219212596495⟩, ⟨208663487389, 230027616357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 120586240 123207680 361103360 367001600 ⟨⟨222176797136, 222176797147⟩, ⟨211601094504, 233016640791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 123207680 125829120 355205120 361103360 ⟨⟨215985225749, 215985225755⟩, ⟨205569013285, 226663333690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 123207680 125829120 361103360 367001600 ⟨⟨218921837417, 218921837424⟩, ⟨208478461670, 229625446049⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 125829120 343408640 367001600 t = true :=
  ⟨_, (join_su (m := 120586240) (by decide) (join_sr (m := 355205120) (by decide) (join_su (m := 117964800) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 349306880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 117964800) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 361103360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 355205120) (by decide) (join_su (m := 123207680) (by decide) (join_sr (m := 349306880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 349306880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 123207680) (by decide) (join_sr (m := 361103360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 361103360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (131/320 : ℝ) (7/16 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((343408640 : ℤ) : ℝ) / (D : ℝ)) = (131/320 : ℝ) := by norm_num [D]
  have e3 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
