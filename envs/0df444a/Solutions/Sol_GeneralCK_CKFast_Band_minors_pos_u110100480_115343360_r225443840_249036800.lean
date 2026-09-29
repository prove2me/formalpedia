-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u110100480_115343360_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:36:26.109223+00:00
-- url     : https://prove2.me/submissions/c9f6cf8b-c357-4e22-aad3-d6cf59c3dcb0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/160, 11/80]`, `ρ ∈ [43/160, 19/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 110100480 111411200 225443840 231342080 ⟨⟨161267414581, 161267414592⟩, ⟨154572029438, 168096785646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 111411200 112721920 225443840 231342080 ⟨⟨159890496775, 159890496786⟩, ⟨153251621983, 166661656245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 111411200 231342080 237240320 ⟨⟨164773089361, 164773089371⟩, ⟨158060311290, 171618710061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 111411200 112721920 231342080 237240320 ⟨⟨163375481034, 163375481045⟩, ⟨156719002991, 170163139739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 112721920 114032640 225443840 231342080 ⟨⟨158529671521, 158529671531⟩, ⟨151946403593, 165243556356⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 114032640 115343360 225443840 231342080 ⟨⟨157184594835, 157184594840⟩, ⟨150656052177, 163842119220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 112721920 114032640 231342080 237240320 ⟨⟨161994015443, 161994015452⟩, ⟨155392946136, 168724635615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 114032640 115343360 231342080 237240320 ⟨⟨160628350510, 160628350512⟩, ⟨154081820037, 167302833384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 110100480 111411200 237240320 243138560 ⟨⟨168254947911, 168254947922⟩, ⟨161525175262, 175116426129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 111411200 112721920 237240320 243138560 ⟨⟨166837097579, 166837097588⟩, ⟨160163407808, 173640869642⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 110100480 111411200 243138560 249036800 ⟨⟨171713487636, 171713487647⟩, ⟨164967105402, 178590444646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 111411200 112721920 243138560 249036800 ⟨⟨170275829973, 170275829984⟩, ⟨163585307075, 177095342491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 112721920 114032640 237240320 243138560 ⟨⟨165435432246, 165435432254⟩, ⟨158816946269, 172182408144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 114032640 115343360 237240320 243138560 ⟨⟨164049611869, 164049611873⟩, ⟨157485471493, 170740679911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 112721920 114032640 243138560 249036800 ⟨⟨168854392055, 168854392064⟩, ⟨162218861604, 175617356635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 114032640 115343360 243138560 249036800 ⟨⟨167448835989, 167448835994⟩, ⟨160867451507, 174156128042⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 110100480 115343360 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 112721920) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 111411200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 111411200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 114032640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 114032640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 112721920) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 111411200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 111411200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 243138560) (by decide) (join_su (m := 114032640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 114032640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/160 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
