-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_199229440_r571473920_593756160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:01:31.093058+00:00
-- url     : https://prove2.me/submissions/ecaf0472-5203-4672-91c2-24c6358d03e2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 19/80]`, `ρ ∈ [109/160, 453/640]` by 15 cells of the computing
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
theorem cell0 : cellOK 188743680 191365120 571473920 577044480 ⟨⟨227826804253, 227826804256⟩, ⟨218918378454, 236909390853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 191365120 577044480 582615040 ⟨⟨229789149660, 229789149665⟩, ⟨220853876739, 238898267310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 193986560 571473920 577044480 ⟨⟨224656389233, 224656389243⟩, ⟨215822104947, 233663877126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 191365120 193986560 577044480 582615040 ⟨⟨226597769724, 226597769733⟩, ⟨217736558057, 235631900521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 191365120 582615040 593756160 ⟨⟨232727301886, 232727301889⟩, ⟨222198681510, 243498673779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 191365120 193986560 582615040 588185600 ⟨⟨228536379486, 228536379496⟩, ⟨219648287951, 237597100458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 191365120 193986560 588185600 593756160 ⟨⟨230472257658, 230472257667⟩, ⟨221557332986, 239559516851⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 193986560 196608000 571473920 577044480 ⟨⟨221509331997, 221509332006⟩, ⟨212748271782, 230442639285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 193986560 196608000 577044480 582615040 ⟨⟨223429658156, 223429658165⟩, ⟨214641602795, 232389706754⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 196608000 199229440 571473920 577044480 ⟨⟨218385096354, 218385096363⟩, ⟨209696362065, 227245122223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 196608000 199229440 577044480 582615040 ⟨⟨220284282680, 220284282689⟩, ⟨211568497560, 229171135256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 193986560 196608000 582615040 588185600 ⟨⟨225347309310, 225347309320⟩, ⟨216532303684, 234334049177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 193986560 196608000 588185600 593756160 ⟨⟨227262322982, 227262322991⟩, ⟨218420411228, 236275704809⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 196608000 199229440 582615040 588185600 ⟨⟨222180887574, 222180887583⟩, ⟨213438093891, 231094519486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 196608000 199229440 588185600 593756160 ⟨⟨224074946992, 224074947001⟩, ⟨215305186316, 233015311565⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 199229440 571473920 593756160 t = true :=
  ⟨_, (join_su (m := 193986560) (by decide) (join_sr (m := 582615040) (by decide) (join_su (m := 191365120) (by decide) (join_sr (m := 577044480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 577044480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 191365120) (by decide) (leaf_ok cell4) (join_sr (m := 588185600) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 582615040) (by decide) (join_su (m := 196608000) (by decide) (join_sr (m := 577044480) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 577044480) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 196608000) (by decide) (join_sr (m := 588185600) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 588185600) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (453/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
