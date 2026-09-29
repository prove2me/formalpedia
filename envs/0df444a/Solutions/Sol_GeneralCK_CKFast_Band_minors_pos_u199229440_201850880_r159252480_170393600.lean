-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_201850880_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:52:43.066849+00:00
-- url     : https://prove2.me/submissions/84b224c3-23de-4cb8-a0fa-1c1240b8680e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 77/320]`, `ρ ∈ [243/1280, 13/64]` by 17 cells of the computing
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
theorem cell0 : cellOK 199229440 199884800 159252480 162037760 ⟨⟨66408837560, 66408837566⟩, ⟨64448641767, 68384940924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199884800 200540160 159252480 162037760 ⟨⟨66127298451, 66127298457⟩, ⟨64172695349, 68097735318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 199884800 162037760 164823040 ⟨⟨67508133971, 67508133977⟩, ⟨65543450278, 69488725453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 199884800 200540160 162037760 164823040 ⟨⟨67222333777, 67222333783⟩, ⟨65263254828, 69197246971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 200540160 201195520 159252480 162037760 ⟨⟨65846764657, 65846764663⟩, ⟨63897724356, 67811565469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 201195520 201850880 159252480 160645120 ⟨⟨65295353088, 65295353089⟩, ⟨63676733480, 66924586339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201195520 201850880 160645120 162037760 ⟨⟨65839007486, 65839007490⟩, ⟨64218362946, 67470268684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 200540160 201195520 162037760 164823040 ⟨⟨66937549582, 66937549588⟩, ⟨64984045488, 68906814926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 201195520 201850880 162037760 164823040 ⟨⟨66653773247, 66653773249⟩, ⟨64705814369, 68617420916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 199229440 199884800 164823040 167608320 ⟨⟨68605855771, 68605855777⟩, ⟨66636694132, 70590925305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 199884800 200540160 164823040 167608320 ⟨⟨68315812453, 68315812460⟩, ⟨66352267445, 70295192080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 199229440 199884800 167608320 170393600 ⟨⟨69702012124, 69702012131⟩, ⟨67728382427, 71691549712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 199884800 200540160 167608320 170393600 ⟨⟨69407743509, 69407743516⟩, ⟨67439742157, 71391579740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 200540160 201195520 164823040 167608320 ⟨⟨68026795642, 68026795648⟩, ⟨66068837371, 70000515794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 201195520 201850880 164823040 167608320 ⟨⟨67738797132, 67738797135⟩, ⟨65786395963, 69706887979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 200540160 201195520 167608320 170393600 ⟨⟨69114511726, 69114511733⟩, ⟨67152108831, 71092677025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 201195520 201850880 167608320 170393600 ⟨⟨68822308510, 68822308515⟩, ⟨66865474436, 70794833043⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 201850880 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 199884800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell4) (join_sr (m := 160645120) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 201195520) (by decide) (leaf_ok cell7) (leaf_ok cell8)))) (join_su (m := 200540160) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 199884800) (by decide) (leaf_ok cell9) (leaf_ok cell10)) (join_su (m := 199884800) (by decide) (leaf_ok cell11) (leaf_ok cell12))) (join_sr (m := 167608320) (by decide) (join_su (m := 201195520) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_su (m := 201195520) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (77/320 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
