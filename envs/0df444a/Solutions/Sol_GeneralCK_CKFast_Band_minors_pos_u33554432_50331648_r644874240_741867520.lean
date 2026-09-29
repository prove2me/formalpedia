-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r644874240_741867520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:56:54.248856+00:00
-- url     : https://prove2.me/submissions/f6bdcd65-3026-407e-a468-6cdf98b1354a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 3/50]`, `ρ ∈ [123/160, 283/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 33554432 37748736 644874240 669122560 ⟨⟨530528104855, 530528104871⟩, ⟨494849412517, 566658436271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 37748736 41943040 644874240 669122560 ⟨⟨519778132100, 519778132115⟩, ⟨484816940140, 555243412292⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 33554432 37748736 669122560 693370880 ⟨⟨541725891182, 541725891199⟩, ⟨506369605862, 577440489866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 37748736 41943040 669122560 693370880 ⟨⟨531018125264, 531018125279⟩, ⟨496341489156, 566108618910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 41943040 46137344 644874240 669122560 ⟨⟨509385168114, 509385168129⟩, ⟨475108752284, 544210424381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 46137344 50331648 644874240 669122560 ⟨⟨499315695492, 499315695507⟩, ⟨465695854578, 533522884557⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 41943040 46137344 669122560 693370880 ⟨⟨520653937824, 520653937838⟩, ⟨486626789917, 555142827476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 46137344 50331648 669122560 693370880 ⟨⟨510601009800, 510601009813⟩, ⟨477197481610, 544507934573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 33554432 37748736 693370880 717619200 ⟨⟨552811611580, 552811611596⟩, ⟨517762575517, 588130349970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 37748736 41943040 693370880 717619200 ⟨⟨542143945507, 542143945523⟩, ⟨507738860778, 576876997518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 33554432 37748736 717619200 741867520 ⟨⟨563798131273, 563798131289⟩, ⟨529042005258, 598739489695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 37748736 41943040 717619200 741867520 ⟨⟨553168406414, 553168406429⟩, ⟨519022493740, 587560218042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 41943040 46137344 693370880 717619200 ⟨⟨531807141107, 531807141124⟩, ⟨498018182445, 565974725828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 46137344 50331648 693370880 717619200 ⟨⟨521769985192, 521769985207⟩, ⟨488573413242, 555389645101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 41943040 46137344 717619200 741867520 ⟨⟨542857476728, 542857476744⟩, ⟨509296087742, 576717891386⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 46137344 50331648 717619200 741867520 ⟨⟨532835153370, 532835153386⟩, ⟨499836498073, 566179809982⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 50331648 644874240 741867520 t = true :=
  ⟨_, (join_sr (m := 693370880) (by decide) (join_su (m := 41943040) (by decide) (join_sr (m := 669122560) (by decide) (join_su (m := 37748736) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 37748736) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 669122560) (by decide) (join_su (m := 46137344) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 46137344) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 41943040) (by decide) (join_sr (m := 717619200) (by decide) (join_su (m := 37748736) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 37748736) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 717619200) (by decide) (join_su (m := 46137344) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 46137344) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (123/160 : ℝ) (283/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((644874240 : ℤ) : ℝ) / (D : ℝ)) = (123/160 : ℝ) := by norm_num [D]
  have e3 : (((741867520 : ℤ) : ℝ) / (D : ℝ)) = (283/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
