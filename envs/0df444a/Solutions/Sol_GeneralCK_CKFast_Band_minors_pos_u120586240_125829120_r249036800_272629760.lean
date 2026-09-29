-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u120586240_125829120_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:38:35.425699+00:00
-- url     : https://prove2.me/submissions/fb1afd29-ab92-4ba6-8a1d-11b01748dafa

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/160, 3/20]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 120586240 121896960 249036800 254935040 ⟨⟨163929610618, 163929610622⟩, ⟨157589171904, 170387878317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 121896960 123207680 249036800 254935040 ⟨⟨162593649238, 162593649249⟩, ⟨156302527865, 169001261377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 120586240 121896960 254935040 260833280 ⟨⟨167191839195, 167191839199⟩, ⟨160833956990, 173666697598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 121896960 123207680 254935040 260833280 ⟨⟨165837125602, 165837125610⟩, ⟨159528410684, 172261507217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 123207680 124518400 249036800 254935040 ⟨⟨161271494262, 161271494272⟩, ⟨155028978985, 167629185527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 124518400 125829120 249036800 254935040 ⟨⟨159962876246, 159962876256⟩, ⟨153768271441, 166271365154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 123207680 124518400 254935040 260833280 ⟨⟨164496254609, 164496254619⟩, ⟨158236004618, 170870884358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 124518400 125829120 254935040 260833280 ⟨⟨163168958209, 163168958219⟩, ⟨156956486070, 169494545220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 120586240 121896960 260833280 266731520 ⟨⟨170435158496, 170435158498⟩, ⟨164060138149, 176926304940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 121896960 123207680 260833280 266731520 ⟨⟨169062039636, 169062039644⟩, ⟨162736031206, 175502893036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 121896960 266731520 272629760 ⟨⟨173659929754, 173659929758⟩, ⟨167268067663, 180167070575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 121896960 123207680 266731520 272629760 ⟨⟨172268742961, 172268742971⟩, ⟨165925732373, 178725779180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 123207680 124518400 260833280 266731520 ⟨⟨167702793825, 167702793833⟩, ⟨161425103849, 174094069348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 124518400 125829120 260833280 266731520 ⟨⟨166357154577, 166357154585⟩, ⟨160127104548, 172699551953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 123207680 124518400 266731520 272629760 ⟨⟨170891454172, 170891454180⟩, ⟨164596610537, 177299091207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 124518400 125829120 266731520 272629760 ⟨⟨169527798501, 169527798510⟩, ⟨163280451890, 175886726697⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 120586240 125829120 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 123207680) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 121896960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 121896960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 124518400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 124518400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 123207680) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 121896960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 121896960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 266731520) (by decide) (join_su (m := 124518400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 124518400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
