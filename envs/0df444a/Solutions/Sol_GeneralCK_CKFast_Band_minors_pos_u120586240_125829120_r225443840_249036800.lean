-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u120586240_125829120_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:37:35.390067+00:00
-- url     : https://prove2.me/submissions/0fd14785-a4f9-4020-8b09-f0e499df3810

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/160, 3/20]`, `ρ ∈ [43/160, 19/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 120586240 121896960 225443840 231342080 ⟨⟨150684073490, 150684073494⟩, ⟨144416652323, 157072760502⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 121896960 123207680 225443840 231342080 ⟨⟨149426794261, 149426794271⟩, ⟨143209231368, 155764166414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 120586240 121896960 231342080 237240320 ⟨⟨154025726869, 154025726872⟩, ⟨147739544940, 160432311696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 121896960 123207680 231342080 237240320 ⟨⟨152748204865, 152748204873⟩, ⟨146511755513, 159103630647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 123207680 124518400 225443840 231342080 ⟨⟨148183113541, 148183113551⟩, ⟨142014662482, 154469944438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 124518400 125829120 225443840 231342080 ⟨⟨146952757159, 146952757169⟩, ⟨140832688505, 153189802718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 123207680 124518400 231342080 237240320 ⟨⟨151484343400, 151484343410⟩, ⟨145296888915, 157789374051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 124518400 125829120 231342080 237240320 ⟨⟨150233869318, 150233869328⟩, ⟨144094688648, 156489251450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 120586240 121896960 237240320 243138560 ⟨⟨157346937640, 157346937645⟩, ⟨151042339317, 163771078360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 121896960 123207680 237240320 243138560 ⟨⟨156049561613, 156049561621⟩, ⟨149794563588, 162422705331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 121896960 243138560 249036800 ⟨⟨160648102975, 160648102979⟩, ⟨154325422361, 167089467990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 121896960 123207680 243138560 249036800 ⟨⟨159331250694, 159331250704⟩, ⟨153058031859, 165721786644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 123207680 124518400 237240320 243138560 ⟨⟨154765901246, 154765901254⟩, ⟨148559774592, 161088802152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 124518400 125829120 237240320 243138560 ⟨⟨153495684514, 153495684524⟩, ⟨147337716615, 159769079879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 123207680 124518400 243138560 249036800 ⟨⟨158028162598, 158028162606⟩, ⟨151803685439, 164368613925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 124518400 125829120 243138560 249036800 ⟨⟨156738567900, 156738567908⟩, ⟨150562128279, 163029662507⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 120586240 125829120 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 123207680) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 121896960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 121896960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 124518400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 124518400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 123207680) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 121896960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 121896960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 243138560) (by decide) (join_su (m := 124518400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 124518400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
