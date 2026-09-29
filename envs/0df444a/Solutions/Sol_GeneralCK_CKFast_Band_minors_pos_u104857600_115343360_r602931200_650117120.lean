-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_115343360_r602931200_650117120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:51:10.698227+00:00
-- url     : https://prove2.me/submissions/bc30f8b5-90ed-4415-982c-e150ac0908f1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 11/80]`, `ρ ∈ [23/32, 31/40]` by 11 cells of the computing
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
theorem cell0 : cellOK 104857600 107479040 602931200 614727680 ⟨⟨361554408287, 361554408301⟩, ⟨346637090045, 376759252844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 107479040 110100480 602931200 614727680 ⟨⟨357139215238, 357139215251⟩, ⟨342379442678, 372186145222⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 104857600 110100480 614727680 626524160 ⟨⟨364631115057, 364631115070⟩, ⟨340563292557, 389452728042⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110100480 112721920 602931200 614727680 ⟨⟨352775159006, 352775159015⟩, ⟨338170535970, 367666474173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 112721920 115343360 602931200 614727680 ⟨⟨348460754448, 348460754460⟩, ⟨334008951026, 363198694749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 110100480 112721920 614727680 626524160 ⟨⟨358022016986, 358022016992⟩, ⟨343389258600, 372934941520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 112721920 115343360 614727680 626524160 ⟨⟨353677372328, 353677372342⟩, ⟨339195355658, 368439242485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 104857600 110100480 626524160 638320640 ⟨⟨369894716147, 369894716159⟩, ⟨345765119124, 394761116963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 104857600 110100480 638320640 650117120 ⟨⟨375132217113, 375132217126⟩, ⟨350941494656, 400042817219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 110100480 115343360 626524160 638320640 ⟨⟨361049421632, 361049421643⟩, ⟨337362603274, 385475070326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 110100480 115343360 638320640 650117120 ⟨⟨366230119371, 366230119383⟩, ⟨342475801698, 390707540137⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 115343360 602931200 650117120 t = true :=
  ⟨_, (join_sr (m := 626524160) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 614727680) (by decide) (join_su (m := 107479040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 614727680) (by decide) (join_su (m := 112721920) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 112721920) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 110100480) (by decide) (join_sr (m := 638320640) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 638320640) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (23/32 : ℝ) (31/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  have e3 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
