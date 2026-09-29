-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r593756160_616038400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:01:56.465151+00:00
-- url     : https://prove2.me/submissions/814e39b8-94a0-45e0-aca2-353c5d9a8ea9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [453/640, 47/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 593756160 599326720 ⟨⟨222780216438, 222780216447⟩, ⟨214054784804, 231675174037⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 201850880 599326720 604897280 ⟨⟨224648426846, 224648426855⟩, ⟨215896055168, 233570108982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 204472320 593756160 599326720 ⟨⟨219615401218, 219615401223⟩, ⟨210960408951, 228439079197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 599326720 604897280 ⟨⟨221462660405, 221462660408⟩, ⟨212780685387, 230313133845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 201850880 604897280 610467840 ⟨⟨226514283534, 226514283544⟩, ⟨217735008885, 235462648061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 201850880 610467840 616038400 ⟨⟨228377819956, 228377819966⟩, ⟨219571678767, 237352825357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 204472320 604897280 610467840 ⟨⟨223307649431, 223307649435⟩, ⟨214598726332, 232184878665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201850880 204472320 610467840 616038400 ⟨⟨225150400356, 225150400360⟩, ⟨216414563239, 234054346309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 207093760 593756160 599326720 ⟨⟨216471568527, 216471568536⟩, ⟨207886216105, 225224765030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 204472320 207093760 599326720 604897280 ⟨⟨218297793618, 218297793627⟩, ⟨209685426787, 227077844626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 209715200 593756160 599326720 ⟨⟨213348247662, 213348247670⟩, ⟨204831751410, 222031745349⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207093760 209715200 599326720 604897280 ⟨⟨215153359145, 215153359154⟩, ⟨206609827521, 223863758867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 604897280 610467840 ⟨⟨220121830190, 220121830200⟩, ⟨211482481241, 228928698494⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 204472320 207093760 610467840 616038400 ⟨⟨221943708952, 221943708962⟩, ⟨213277409606, 230777357900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 209715200 604897280 610467840 ⟨⟨216956361841, 216956361850⟩, ⟨208385824790, 225693628821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 209715200 610467840 616038400 ⟨⟨218757285152, 218757285161⟩, ⟨210159772083, 227521385135⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 593756160 616038400 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 604897280) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 599326720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 599326720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 201850880) (by decide) (join_sr (m := 610467840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 610467840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 604897280) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 599326720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 599326720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 207093760) (by decide) (join_sr (m := 610467840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 610467840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (453/640 : ℝ) (47/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  have e3 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
