-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r749731840_772014080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:08:15.900982+00:00
-- url     : https://prove2.me/submissions/5f22d9d7-0c15-4f43-b3b6-77472aa1ab10

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [143/160, 589/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 749731840 760872960 ⟨⟨260384546471, 260384546481⟩, ⟨249785306907, 271201881719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 212336640 214958080 749731840 760872960 ⟨⟨256720675679, 256720675689⟩, ⟨246212430361, 267446458540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 212336640 760872960 772014080 ⟨⟨263856244575, 263856244586⟩, ⟨253201483232, 274728174770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 760872960 772014080 ⟨⟨260153342765, 260153342776⟩, ⟨249589448846, 270933925742⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 217579520 749731840 755302400 ⟨⟨252224254533, 252224254538⟩, ⟨243160047465, 261449528298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214958080 217579520 755302400 760872960 ⟨⟨253922172666, 253922172670⟩, ⟨244831412844, 263173807183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 217579520 220200960 749731840 755302400 ⟨⟨248603057309, 248603057319⟩, ⟨239604498120, 257762536440⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 217579520 220200960 755302400 760872960 ⟨⟨250281199391, 250281199401⟩, ⟨241256054184, 259467098905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 760872960 766443520 ⟨⟨255618878088, 255618878093⟩, ⟨246501576772, 264896857032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 217579520 766443520 772014080 ⟨⟨257314392924, 257314392927⟩, ⟨248170560965, 266618700347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 760872960 766443520 ⟨⟨251958172711, 251958172721⟩, ⟨242906451227, 261170477901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 220200960 766443520 772014080 ⟨⟨253633998494, 253633998502⟩, ⟨244555710089, 262872695012⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 749731840 772014080 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 760872960) (by decide) (join_su (m := 212336640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 212336640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 760872960) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 755302400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 755302400) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 217579520) (by decide) (join_sr (m := 766443520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 766443520) (by decide) (leaf_ok cell10) (leaf_ok cell11)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (143/160 : ℝ) (589/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  have e3 : (((772014080 : ℤ) : ℝ) / (D : ℝ)) = (589/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
