-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r794296320_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:12:01.918002+00:00
-- url     : https://prove2.me/submissions/b598b661-8525-4471-8420-ff28e29f1884

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [303/320, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 794296320 805437440 ⟨⟨305397829082, 305397829089⟩, ⟨293832842307, 317177475022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 191365120 193986560 794296320 805437440 ⟨⟨301441223672, 301441223682⟩, ⟨289971301360, 313125913528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 191365120 805437440 816578560 ⟨⟨309148161597, 309148161600⟩, ⟨297530129089, 320979116152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 805437440 816578560 ⟨⟨305155284503, 305155284514⟩, ⟨293631940991, 316891754255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 193986560 196608000 794296320 805437440 ⟨⟨297503095965, 297503095976⟩, ⟨286127639480, 309093379457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 196608000 199229440 794296320 805437440 ⟨⟨293583066200, 293583066211⟩, ⟨282301483341, 305079488154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 193986560 196608000 805437440 816578560 ⟨⟨301180599389, 301180599399⟩, ⟨289751376469, 312823101782⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 196608000 199229440 805437440 816578560 ⟨⟨297223733734, 297223733745⟩, ⟨285888068764, 308772782017⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 191365120 816578560 827719680 ⟨⟨312892890805, 312892890812⟩, ⟨301221916103, 324775022609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 191365120 193986560 816578560 827719680 ⟨⟨308863911242, 308863911253⟩, ⟨297287244854, 320652034868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 191365120 827719680 838860800 ⟨⟨316632263036, 316632263043⟩, ⟨304908443520, 328565446505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 191365120 193986560 827719680 838860800 ⟨⟨312567341660, 312567341671⟩, ⟨300937444808, 324406998711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 816578560 827719680 ⟨⟨304852835527, 304852835537⟩, ⟨293369939164, 316547436321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 199229440 816578560 827719680 ⟨⟨300859298323, 300859298333⟩, ⟨289469638792, 312460858099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 193986560 196608000 827719680 838860800 ⟨⟨308520033798, 308520033809⟩, ⟨296983551300, 320266617840⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 196608000 199229440 827719680 838860800 ⟨⟨304489981225, 304489981235⟩, ⟨293046409227, 316143942791⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 794296320 838860800 t = true :=
  ⟨_, (join_sr (m := 816578560) (by decide) (join_su (m := 193986560) (by decide) (join_sr (m := 805437440) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 191365120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 805437440) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 196608000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 193986560) (by decide) (join_sr (m := 827719680) (by decide) (join_su (m := 191365120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 191365120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 827719680) (by decide) (join_su (m := 196608000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 196608000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (303/320 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
