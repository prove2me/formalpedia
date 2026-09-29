-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u120586240_125829120_r178257920_190054400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:34:10.029998+00:00
-- url     : https://prove2.me/submissions/8ccfaf2d-46d7-4d1c-a35f-3bfa800cf9fa

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/160, 3/20]`, `ρ ∈ [17/80, 29/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 120586240 121896960 178257920 181207040 ⟨⟨122279891852, 122279891856⟩, ⟨117443286363, 127196926722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 120586240 121896960 181207040 184156160 ⟨⟨124046342994, 124046342996⟩, ⟨119199687004, 128973204602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 121896960 123207680 178257920 181207040 ⟨⟨121206027465, 121206027473⟩, ⟨116406516998, 126084968436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 121896960 123207680 181207040 184156160 ⟨⟨122960454707, 122960454715⟩, ⟨118150880029, 127849245436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 120586240 121896960 184156160 187105280 ⟨⟨125806701430, 125806701435⟩, ⟨120950081578, 130743302850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 120586240 121896960 187105280 190054400 ⟨⟨127561029374, 127561029379⟩, ⟨122694531005, 132507284985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 121896960 123207680 184156160 187105280 ⟨⟨124708914941, 124708914951⟩, ⟨119889360678, 129607470477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 121896960 123207680 187105280 190054400 ⟨⟨126451468504, 126451468512⟩, ⟨121622018037, 131359705148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 123207680 124518400 178257920 181207040 ⟨⟨120144939725, 120144939733⟩, ⟨115381911913, 124986420057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 123207680 124518400 181207040 184156160 ⟨⟨121887410883, 121887410891⟩, ⟨117114307946, 126738760867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 124518400 125829120 178257920 181207040 ⟨⟨119096352122, 119096352130⟩, ⟨114369209710, 123900989372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 124518400 125829120 181207040 184156160 ⟨⟨120826934775, 120826934783⟩, ⟨116089708986, 125641458594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 123207680 124518400 184156160 187105280 ⟨⟨123624038141, 123624038149⟩, ⟨118840942727, 128485174766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 123207680 124518400 187105280 190054400 ⟨⟨125354880015, 125354880025⟩, ⟨120561873577, 130225721484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 124518400 125829120 184156160 187105280 ⟨⟨122551794104, 122551794112⟩, ⟨117804565644, 127376123392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 124518400 125829120 187105280 190054400 ⟨⟨124270986865, 124270986873⟩, ⟨119513835289, 129105041686⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 120586240 125829120 178257920 190054400 t = true :=
  ⟨_, (join_su (m := 123207680) (by decide) (join_sr (m := 184156160) (by decide) (join_su (m := 121896960) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 181207040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 121896960) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 187105280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184156160) (by decide) (join_su (m := 124518400) (by decide) (join_sr (m := 181207040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 181207040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 124518400) (by decide) (join_sr (m := 187105280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 187105280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (17/80 : ℝ) (29/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e3 : (((190054400 : ℤ) : ℝ) / (D : ℝ)) = (29/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
