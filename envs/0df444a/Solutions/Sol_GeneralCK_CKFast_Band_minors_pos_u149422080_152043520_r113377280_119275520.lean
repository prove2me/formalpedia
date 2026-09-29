-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u149422080_152043520_r113377280_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:09:36.693071+00:00
-- url     : https://prove2.me/submissions/d65e100e-eb65-4eab-9492-a583c73054b7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [57/320, 29/160]`, `ρ ∈ [173/1280, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 149422080 150077440 113377280 114851840 ⟨⟨66558740277, 66558740284⟩, ⟨64593549545, 68539994711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 149422080 150077440 114851840 116326400 ⟨⟨67366747916, 67366747924⟩, ⟨65398766656, 69350785016⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 150077440 150732800 113377280 114851840 ⟨⟨66263580406, 66263580414⟩, ⟨64304869651, 68238260703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 150077440 150732800 114851840 116326400 ⟨⟨67068399782, 67068399789⟩, ⟨65106905956, 69045855556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 149422080 150077440 116326400 117800960 ⟨⟨68173580888, 68173580894⟩, ⟨66202817278, 70160392418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 149422080 150077440 117800960 119275520 ⟨⟨68979244330, 68979244338⟩, ⟨67005706506, 70968822108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 150077440 150732800 116326400 117800960 ⟨⟨67872057846, 67872057853⟩, ⟨65907789011, 69852280986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 150077440 150732800 117800960 119275520 ⟨⟨68674559657, 68674559663⟩, ⟨66707523824, 70657542098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 150732800 151388160 113377280 114851840 ⟨⟨65970040987, 65970040995⟩, ⟨64017761332, 67938196973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 150732800 151388160 114851840 116326400 ⟨⟨66771685159, 66771685166⟩, ⟨64816629903, 68742609421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 151388160 152043520 113377280 114851840 ⟨⟨65678105293, 65678105300⟩, ⟨63732208425, 67639786222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 151388160 152043520 114851840 116326400 ⟨⟨66476587222, 66476587229⟩, ⟨64527922227, 68441029217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 150732800 151388160 116326400 117800960 ⟨⟨67572181223, 67572181231⟩, ⟨65614358306, 69545865773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 150732800 151388160 117800960 119275520 ⟨⟨68371534158, 68371534164⟩, ⟨66410951472, 70347971048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 151388160 152043520 116326400 117800960 ⟨⟨67273934098, 67273934104⟩, ⟨65322508798, 69241129286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 151388160 152043520 117800960 119275520 ⟨⟨68070150815, 68070150823⟩, ⟨66115972987, 70040091369⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 149422080 152043520 113377280 119275520 t = true :=
  ⟨_, (join_su (m := 150732800) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 150077440) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 114851840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 150077440) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 117800960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 116326400) (by decide) (join_su (m := 151388160) (by decide) (join_sr (m := 114851840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 114851840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 151388160) (by decide) (join_sr (m := 117800960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 117800960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (57/320 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (173/1280 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((149422080 : ℤ) : ℝ) / (D : ℝ)) = (57/320 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
