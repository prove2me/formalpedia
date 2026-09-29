-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r749731840_794296320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:26:59.464964+00:00
-- url     : https://prove2.me/submissions/9f39e0c0-4c8b-4f9c-9310-4693deb6aeff

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [143/160, 303/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 749731840 760872960 ⟨⟨321570529945, 321570529956⟩, ⟨309419665443, 333943272219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 170393600 173015040 749731840 760872960 ⟨⟨317588136951, 317588136962⟩, ⟨305539913116, 329858347543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 170393600 760872960 772014080 ⟨⟨325631247409, 325631247421⟩, ⟨313430879690, 338051018761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 760872960 772014080 ⟨⟨321614307915, 321614307927⟩, ⟨309515953496, 333932288767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 175636480 749731840 760872960 ⟨⟨313629000765, 313629000776⟩, ⟨301682613216, 325797429784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 175636480 178257920 749731840 760872960 ⟨⟨309692621048, 309692621052⟩, ⟨297847276821, 321760009156⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 173015040 175636480 760872960 772014080 ⟨⟨317620282488, 317620282499⟩, ⟨305623174463, 329837183094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 175636480 178257920 760872960 772014080 ⟨⟨313648680312, 313648680318⟩, ⟨301752062276, 325765202427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 170393600 772014080 783155200 ⟨⟨329683601702, 329683601715⟩, ⟨317433902776, 342150204791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 173015040 772014080 783155200 ⟨⟨325632343736, 325632343747⟩, ⟨313484026236, 337997901638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167772160 170393600 783155200 794296320 ⟨⟨333727931965, 333727931975⟩, ⟨321429065143, 346241177711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 170393600 173015040 783155200 794296320 ⟨⟨329642572516, 329642572527⟩, ⟨317444451028, 342055522263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 173015040 175636480 772014080 783155200 ⟨⟨321603654569, 321603654580⟩, ⟨309555988760, 333868838068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 175636480 178257920 772014080 783155200 ⟨⟨317597052797, 317597052804⟩, ⟨305649318549, 329762525077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 173015040 175636480 783155200 794296320 ⟨⟨325579434312, 325579434325⟩, ⟨313481365285, 337892719740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 783155200 794296320 ⟨⟨321538045238, 321538045246⟩, ⟨309539344537, 333752291307⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 749731840 794296320 t = true :=
  ⟨_, (join_sr (m := 772014080) (by decide) (join_su (m := 173015040) (by decide) (join_sr (m := 760872960) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 170393600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 760872960) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 175636480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 173015040) (by decide) (join_sr (m := 783155200) (by decide) (join_su (m := 170393600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 170393600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 783155200) (by decide) (join_su (m := 175636480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 175636480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (143/160 : ℝ) (303/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  have e3 : (((794296320 : ℤ) : ℝ) / (D : ℝ)) = (303/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
