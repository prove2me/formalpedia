-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_154664960_r125173760_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:10:19.002702+00:00
-- url     : https://prove2.me/submissions/bb3dad23-0c22-4b15-99e4-51b957377d46

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 59/320]`, `ρ ∈ [191/1280, 5/32]` by 8 cells of the computing
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
theorem cell0 : cellOK 152043520 152698880 125173760 128122880 ⟨⟨72112645134, 72112645137⟩, ⟨69663263894, 74586672792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 152698880 153354240 125173760 128122880 ⟨⟨71797607629, 71797607637⟩, ⟨69357024112, 74262684913⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 152043520 152698880 128122880 131072000 ⟨⟨73683455151, 73683455157⟩, ⟨71227983872, 76163534316⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 152698880 153354240 128122880 131072000 ⟨⟨73362368478, 73362368485⟩, ⟨70915710358, 75833482773⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 153354240 154009600 125173760 128122880 ⟨⟨71484228129, 71484228135⟩, ⟨69052379863, 73940419001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 154009600 154664960 125173760 128122880 ⟨⟨71172490026, 71172490033⟩, ⟨68749315238, 73619857741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 153354240 154009600 128122880 131072000 ⟨⟨73042962608, 73042962616⟩, ⟨70605055237, 75505175924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 154009600 154664960 128122880 131072000 ⟨⟨72725220778, 72725220785⟩, ⟨70296002438, 75178596292⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 154664960 125173760 131072000 t = true :=
  ⟨_, (join_su (m := 153354240) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 152698880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 152698880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 128122880) (by decide) (join_su (m := 154009600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 154009600) (by decide) (leaf_ok cell6) (leaf_ok cell7))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (59/320 : ℝ) →
    rho ∈ Set.Icc (191/1280 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e2 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
