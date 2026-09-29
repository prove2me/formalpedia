-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u144179200_146800640_r95682560_101580800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:18:26.601577+00:00
-- url     : https://prove2.me/submissions/3fb142f6-68d9-4c67-accf-20b325a0dace

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/64, 7/40]`, `ρ ∈ [73/640, 31/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 144179200 144834560 95682560 97157120 ⟨⟨58869892482, 58869892490⟩, ⟨56885970240, 60870786068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 144179200 144834560 97157120 98631680 ⟨⟨59719806761, 59719806768⟩, ⟨57732919530, 61723655793⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 144834560 145489920 95682560 97157120 ⟨⟨58601875571, 58601875579⟩, ⟨56624746136, 60595870291⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 144834560 145489920 97157120 98631680 ⟨⟨59448309646, 59448309652⟩, ⟨57468224311, 61445251036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 144179200 144834560 98631680 100106240 ⟨⟨60568360596, 60568360603⟩, ⟨58578518308, 62575155081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 144179200 144834560 100106240 101580800 ⟨⟨61415560281, 61415560288⟩, ⟨59422772809, 63425290288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 144834560 145489920 98631680 100106240 ⟨⟨60293399154, 60293399161⟩, ⟨58310367701, 62293277372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 144834560 145489920 100106240 101580800 ⟨⟨61137150284, 61137150292⟩, ⟨59151182433, 63139955551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 145489920 146145280 95682560 97157120 ⟨⟨58335440920, 58335440923⟩, ⟨56365050569, 60322591632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 145489920 146145280 97157120 98631680 ⟨⟨59178410873, 59178410875⟩, ⟨57205073703, 61168499477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146145280 146800640 95682560 97157120 ⟨⟨58070571301, 58070571307⟩, ⟨56106866963, 60050932201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 146145280 146800640 97157120 98631680 ⟨⟨58910093077, 58910093083⟩, ⟨56943450994, 60893383099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 145489920 146145280 98631680 100106240 ⟨⟨60020051944, 60020051947⟩, ⟨58043777589, 62013068752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 145489920 146145280 100106240 101580800 ⟨⟨60860370218, 60860370221⟩, ⟨58881168248, 62856305599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 146145280 146800640 98631680 100106240 ⟨⟨59748301466, 59748301472⟩, ⟨57778731122, 61734511068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 146145280 146800640 100106240 101580800 ⟨⟨60585202451, 60585202459⟩, ⟨58612713273, 62574322148⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 144179200 146800640 95682560 101580800 t = true :=
  ⟨_, (join_su (m := 145489920) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 144834560) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 97157120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 144834560) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 100106240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 98631680) (by decide) (join_su (m := 146145280) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 97157120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 146145280) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 100106240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/64 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (31/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
