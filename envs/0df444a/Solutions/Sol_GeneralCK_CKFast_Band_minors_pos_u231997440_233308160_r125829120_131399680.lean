-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u231997440_233308160_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:18:50.81676+00:00
-- url     : https://prove2.me/submissions/1ba580e7-ca70-4efd-8d3c-178c436e41b0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [177/640, 89/320]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 231997440 232325120 125829120 127221760 ⟨⟨42395145715, 42395145720⟩, ⟨41560669396, 43232794343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 232325120 232652800 125829120 127221760 ⟨⟨42298807350, 42298807356⟩, ⟨41465390545, 43135389774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231997440 232325120 127221760 128614400 ⟨⟨42850316914, 42850316919⟩, ⟨42014853563, 43688953837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 232325120 232652800 127221760 128614400 ⟨⟨42752992626, 42752992631⟩, ⟨41918590369, 43590561772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 232652800 232980480 125829120 127221760 ⟨⟨42202613704, 42202613710⟩, ⟨41370253930, 43038132428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 232980480 233308160 125829120 127221760 ⟨⟨42106564217, 42106564222⟩, ⟨41275259000, 42941021737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 232652800 232980480 127221760 128614400 ⟨⟨42655814235, 42655814240⟩, ⟨41822470586, 43492318111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 232980480 233308160 127221760 128614400 ⟨⟨42558781177, 42558781182⟩, ⟨41726493660, 43394222282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232325120 128614400 130007040 ⟨⟨43305256899, 43305256904⟩, ⟨42468807001, 44144881630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 232325120 232652800 128614400 130007040 ⟨⟨43206948156, 43206948163⟩, ⟨42371560926, 44045503545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 231997440 232325120 130007040 131399680 ⟨⟨43759966233, 43759966239⟩, ⟨42922530271, 44600578285⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232325120 232652800 130007040 131399680 ⟨⟨43660674500, 43660674505⟩, ⟨42824302772, 44500215648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 232652800 232980480 128614400 130007040 ⟨⟨43108786481, 43108786486⟩, ⟨42274459429, 43946275035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 232980480 233308160 128614400 130007040 ⟨⟨43010771305, 43010771312⟩, ⟨42177501955, 43847195526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 232652800 232980480 130007040 131399680 ⟨⟨43561530997, 43561531002⟩, ⟨42726221011, 44400003753⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232980480 233308160 130007040 131399680 ⟨⟨43462535151, 43462535157⟩, ⟨42628284430, 44299942018⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 231997440 233308160 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 232325120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 232325120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 232980480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 232980480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 232652800) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 232325120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 232325120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 232980480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 232980480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (177/640 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((231997440 : ℤ) : ℝ) / (D : ℝ)) = (177/640 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
