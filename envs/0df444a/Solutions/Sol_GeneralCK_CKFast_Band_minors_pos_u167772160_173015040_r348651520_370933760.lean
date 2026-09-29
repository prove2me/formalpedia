-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_173015040_r348651520_370933760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:46:48.26071+00:00
-- url     : https://prove2.me/submissions/ab75a52f-0309-4017-b45a-96586f1bf845

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 33/160]`, `ρ ∈ [133/320, 283/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 167772160 169082880 348651520 354222080 ⟨⟨165880401513, 165880401521⟩, ⟨160755838903, 171079388241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 169082880 170393600 348651520 354222080 ⟨⟨164647225140, 164647225148⟩, ⟨159552840157, 169815478291⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 167772160 170393600 354222080 359792640 ⟨⟨167592236389, 167592236396⟩, ⟨159128566299, 176257241118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 171704320 348651520 354222080 ⟨⟨163421847975, 163421847982⟩, ⟨158357344391, 168559669955⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 171704320 173015040 348651520 354222080 ⟨⟨162204157385, 162204157392⟩, ⟨157169243505, 167311845977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 170393600 171704320 354222080 359792640 ⟨⟨165731042473, 165731042481⟩, ⟨160650594246, 170884613063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 171704320 173015040 354222080 359792640 ⟨⟨164499889995, 164499890002⟩, ⟨159449017767, 169623349176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 167772160 170393600 359792640 365363200 ⟨⟨169915071670, 169915071677⟩, ⟨161421732709, 178609347866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 167772160 170393600 365363200 370933760 ⟨⟨172231425993, 172231426002⟩, ⟨163708554750, 180954831273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 170393600 171704320 359792640 365363200 ⟨⟨168033846508, 168033846517⟩, ⟨162937539823, 173203078009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 171704320 173015040 359792640 365363200 ⟨⟨166789349544, 166789349553⟩, ⟨161722603236, 171928493520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 170393600 173015040 365363200 370933760 ⟨⟨169700525774, 169700525782⟩, ⟨161264695912, 178334421111⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 173015040 348651520 370933760 t = true :=
  ⟨_, (join_sr (m := 359792640) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 169082880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 354222080) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 171704320) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 170393600) (by decide) (join_sr (m := 365363200) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 365363200) (by decide) (join_su (m := 171704320) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (283/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
