-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r705167360_749731840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:08:57.798046+00:00
-- url     : https://prove2.me/submissions/7b8d1d6e-3d7d-4000-84f1-7b7af5cb47b5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [269/320, 143/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 705167360 716308480 ⟨⟨260648091933, 260648091944⟩, ⟨249898346131, 271622632374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 204472320 705167360 716308480 ⟨⟨257068836305, 257068836309⟩, ⟨246413637022, 267948059685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 201850880 716308480 727449600 ⟨⟨264299122728, 264299122738⟩, ⟨253494157010, 275327723330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 716308480 727449600 ⟨⟨260680925535, 260680925541⟩, ⟨249970301191, 271614499882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 207093760 705167360 716308480 ⟨⟨253508532761, 253508532771⟩, ⟨242947084163, 264293208961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 207093760 209715200 705167360 716308480 ⟨⟨249966780432, 249966780441⟩, ⟨239498298181, 260657668958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 204472320 207093760 716308480 727449600 ⟨⟨257081451243, 257081451252⟩, ⟨246464400280, 267920739107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 207093760 209715200 716308480 727449600 ⟨⟨253500305771, 253500305780⟩, ⟨242976070944, 264246037348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 199229440 201850880 727449600 738590720 ⟨⟨267943425402, 267943425412⟩, ⟨257083365655, 279025935341⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 201850880 204472320 727449600 738590720 ⟨⟨264286512973, 264286512978⟩, ⟨253520581886, 275274295271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199229440 201850880 738590720 749731840 ⟨⟨271581231958, 271581231968⟩, ⟨260666198362, 282717505901⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 201850880 204472320 738590720 749731840 ⟨⟨267885821704, 267885821709⟩, ⟨257064696756, 278927674161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 727449600 738590720 ⟨⟨260648089863, 260648089872⟩, ⟨249975547281, 271541854232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 207093760 209715200 727449600 738590720 ⟨⟨257027768765, 257027768775⟩, ⟨246447884542, 267828216111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 204472320 207093760 738590720 749731840 ⟨⟨264208663042, 264208663052⟩, ⟨253480734409, 275156773719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 209715200 738590720 749731840 ⟨⟨260549375409, 260549375419⟩, ⟨249913940045, 271404415957⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 705167360 749731840 t = true :=
  ⟨_, (join_sr (m := 727449600) (by decide) (join_su (m := 204472320) (by decide) (join_sr (m := 716308480) (by decide) (join_su (m := 201850880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 201850880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 716308480) (by decide) (join_su (m := 207093760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 207093760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 204472320) (by decide) (join_sr (m := 738590720) (by decide) (join_su (m := 201850880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 201850880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 738590720) (by decide) (join_su (m := 207093760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 207093760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (269/320 : ℝ) (143/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  have e3 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
