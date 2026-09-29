-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r208404480_256901120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:28:17.456782+00:00
-- url     : https://prove2.me/submissions/bfadc7de-18cf-4ed2-b78d-8683e17174b1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 3/100]`, `ρ ∈ [159/640, 49/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 18874368 208404480 220528640 ⟨⟨337618369814, 337618369838⟩, ⟨307470866623, 369415897946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 18874368 20971520 208404480 220528640 ⟨⟨328987367627, 328987367647⟩, ⟨299862870505, 359697386397⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 16777216 18874368 220528640 232652800 ⟨⟨346984734129, 346984734153⟩, ⟨317395231929, 378089151097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 18874368 20971520 220528640 232652800 ⟨⟨338437572720, 338437572742⟩, ⟨309813775080, 368522323065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 20971520 23068672 208404480 220528640 ⟨⟨320830606474, 320830606496⟩, ⟨292656423022, 350528453593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 23068672 25165824 208404480 220528640 ⟨⟨313101056517, 313101056539⟩, ⟨285813292563, 341853465874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 20971520 23068672 220528640 232652800 ⟨⟨330344363229, 330344363247⟩, ⟨302619577423, 359477790763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 23068672 25165824 220528640 232652800 ⟨⟨322660843252, 322660843273⟩, ⟨295776391790, 350903584298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 16777216 18874368 232652800 244776960 ⟨⟨356030425202, 356030425224⟩, ⟨326971249473, 386483035677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 18874368 20971520 232652800 244776960 ⟨⟨347567278195, 347567278218⟩, ⟨319421319439, 377061709677⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 16777216 18874368 244776960 256901120 ⟨⟨364785895956, 364785895978⟩, ⟨336231093574, 394624473977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 18874368 20971520 244776960 256901120 ⟨⟨356406299022, 356406299044⟩, ⟨328716514298, 385342618747⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 20971520 23068672 232652800 244776960 ⟨⟨339539261536, 339539261553⟩, ⟨312245116949, 368137766327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 23068672 25165824 232652800 244776960 ⟨⟨331904587200, 331904587221⟩, ⟨305408198658, 359662466838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 20971520 23068672 244776960 256901120 ⟨⟨348444349741, 348444349761⟩, ⟨321562862818, 376535331219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 23068672 25165824 244776960 256901120 ⟨⟨340860480277, 340860480298⟩, ⟨314737338282, 368156736169⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 25165824 208404480 256901120 t = true :=
  ⟨_, (join_sr (m := 232652800) (by decide) (join_su (m := 20971520) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 18874368) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 18874368) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 220528640) (by decide) (join_su (m := 23068672) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 23068672) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 20971520) (by decide) (join_sr (m := 244776960) (by decide) (join_su (m := 18874368) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 18874368) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 244776960) (by decide) (join_su (m := 23068672) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 23068672) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (159/640 : ℝ) (49/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  have e3 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
