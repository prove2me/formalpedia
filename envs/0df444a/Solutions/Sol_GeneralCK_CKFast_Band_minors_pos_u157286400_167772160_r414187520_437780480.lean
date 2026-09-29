-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r414187520_437780480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:08:20.619418+00:00
-- url     : https://prove2.me/submissions/0cbbde9d-3ef7-405b-bff2-132376131bf0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [79/160, 167/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 414187520 420085760 ⟨⟨203676091851, 203676091861⟩, ⟨194426886709, 213136078888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 159907840 420085760 425984000 ⟨⟨206168870593, 206168870603⟩, ⟨196890185203, 215657626601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 162529280 414187520 420085760 ⟨⟨200790721855, 200790721865⟩, ⟨191636625029, 210153259437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 420085760 425984000 ⟨⟨203257873647, 203257873656⟩, ⟨194074116056, 212649414282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 159907840 425984000 431882240 ⟨⟨208654465978, 208654465988⟩, ⟨199346453341, 218171832284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 159907840 431882240 437780480 ⟨⟨211132986840, 211132986850⟩, ⟨201795797130, 220678807627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 162529280 425984000 431882240 ⟨⟨205718080936, 205718080946⟩, ⟨196504809863, 215138471510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 159907840 162529280 431882240 437780480 ⟨⟨208171447786, 208171447796⟩, ⟨198928807845, 217620537888⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 165150720 414187520 420085760 ⟨⟨197939517725, 197939517729⟩, ⟨188878744954, 207206431239⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 162529280 165150720 420085760 425984000 ⟨⟨200380985899, 200380985904⟩, ⟨191290393099, 209677113127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 167772160 414187520 420085760 ⟨⟨195121537390, 195121537400⟩, ⟨186152356050, 204294599838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 165150720 167772160 420085760 425984000 ⟨⟨197537271857, 197537271864⟩, ⟨188538131446, 206739736371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 162529280 165150720 425984000 431882240 ⟨⟨202815742595, 202815742600⟩, ⟨193695471353, 212140935989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 162529280 165150720 431882240 437780480 ⟨⟨205243887293, 205243887297⟩, ⟨196094076682, 214598001857⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 165150720 167772160 425984000 431882240 ⟨⟨199946522107, 199946522117⟩, ⟨190917558562, 209178246702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 165150720 167772160 431882240 437780480 ⟨⟨202349383227, 202349383236⟩, ⟨193290730107, 211610228320⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 414187520 437780480 t = true :=
  ⟨_, (join_su (m := 162529280) (by decide) (join_sr (m := 425984000) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 420085760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 420085760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 159907840) (by decide) (join_sr (m := 431882240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 431882240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 425984000) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 420085760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 420085760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 165150720) (by decide) (join_sr (m := 431882240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 431882240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (79/160 : ℝ) (167/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((414187520 : ℤ) : ℝ) / (D : ℝ)) = (79/160 : ℝ) := by norm_num [D]
  have e3 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
