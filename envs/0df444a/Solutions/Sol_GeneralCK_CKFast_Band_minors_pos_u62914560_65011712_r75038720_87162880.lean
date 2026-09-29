-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u62914560_65011712_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:05:27.238375+00:00
-- url     : https://prove2.me/submissions/6c73e1a4-1b63-43ab-9244-254f732af289

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/40, 31/400]`, `ρ ∈ [229/2560, 133/1280]` by 14 cells of the computing
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
theorem cell0 : cellOK 62914560 63438848 75038720 78069760 ⟨⟨94453278530, 94453278540⟩, ⟨90132276364, 98851174397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 63438848 63963136 75038720 78069760 ⟨⟨93908416821, 93908416835⟩, ⟨89615112413, 98277722189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 62914560 63438848 78069760 81100800 ⟨⟨97664579276, 97664579289⟩, ⟨93336486992, 102068764761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 63438848 63963136 78069760 81100800 ⟨⟨97105715459, 97105715470⟩, ⟨92805245371, 101481403642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 63963136 64487424 75038720 78069760 ⟨⟨93369479257, 93369479270⟩, ⟨89103503813, 97710578984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 64487424 65011712 75038720 78069760 ⟨⟨92836361174, 92836361184⟩, ⟨88597353360, 97149632279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 63963136 64487424 78069760 81100800 ⟨⟨96552868573, 96552868586⟩, ⟨92279655387, 100900440357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 64487424 65011712 78069760 81100800 ⟨⟨96005933256, 96005933269⟩, ⟨91759618993, 100325761841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 62914560 63438848 81100800 84131840 ⟨⟨100843930179, 100843930189⟩, ⟨96509174870, 105253986909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 63438848 63963136 81100800 84131840 ⟨⟨100271462950, 100271462963⟩, ⟨95964248469, 104653121063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 62914560 63963136 84131840 87162880 ⟨⟨103698418978, 103698418991⟩, ⟨97389304513, 110168250814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 63963136 64487424 81100800 84131840 ⟨⟨99705099265, 99705099275⟩, ⟨95425063872, 104058735643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 64487424 65011712 81100800 84131840 ⟨⟨99144733166, 99144733177⟩, ⟨94891522327, 103470717133⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 63963136 65011712 84131840 87162880 ⟨⟨102539389490, 102539389501⟩, ⟨96306209593, 108929816996⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 62914560 65011712 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 63963136) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 63438848) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 63438848) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 64487424) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 64487424) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 63963136) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 63438848) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 84131840) (by decide) (join_su (m := 64487424) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/40 : ℝ) (31/400 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e1 : (((65011712 : ℤ) : ℝ) / (D : ℝ)) = (31/400 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
