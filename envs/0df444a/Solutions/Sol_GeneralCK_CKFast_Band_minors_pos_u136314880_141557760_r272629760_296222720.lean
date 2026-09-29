-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_141557760_r272629760_296222720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:44:10.857992+00:00
-- url     : https://prove2.me/submissions/5ae6cdeb-05b3-4202-84dc-5289f4941b5a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 27/160]`, `ρ ∈ [13/40, 113/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 137625600 272629760 278528000 ⟨⟨160823183438, 160823183448⟩, ⟨154957368216, 166789961455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 137625600 138936320 272629760 278528000 ⟨⟨159565262562, 159565262570⟩, ⟨153740887862, 165489589009⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 137625600 278528000 284426240 ⟨⟨163804168801, 163804168809⟩, ⟨157920565716, 169788173737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 137625600 138936320 278528000 284426240 ⟨⟨162529099815, 162529099823⟩, ⟨156686855799, 168470753937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 138936320 140247040 272629760 278528000 ⟨⟨158318496795, 158318496805⟩, ⟨152535034914, 164200914910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 140247040 141557760 272629760 278528000 ⟨⟨157082690225, 157082690231⟩, ⟨151339623753, 162923732619⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 138936320 140247040 278528000 284426240 ⟨⟨161265216258, 161265216268⟩, ⟨155463809385, 167165056480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 140247040 141557760 278528000 284426240 ⟨⟨160012323089, 160012323095⟩, ⟨154251241527, 165870875922⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 137625600 284426240 290324480 ⟨⟨166771061901, 166771061911⟩, ⟨160869891111, 172772073491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 137625600 138936320 284426240 290324480 ⟨⟨165479101606, 165479101613⟩, ⟨159619204281, 171437867125⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 137625600 290324480 296222720 ⟨⟨169724103955, 169724103963⟩, ⟨163805580205, 175741907391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 137625600 138936320 290324480 296222720 ⟨⟨168415502942, 168415502950⟩, ⟨162538163077, 174391168870⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 138936320 140247040 284426240 290324480 ⟨⟨164198352981, 164198352989⟩, ⟨158379213005, 170115403003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 140247040 141557760 284426240 290324480 ⟨⟨162928621915, 162928621921⟩, ⟨157149733063, 168804476829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 138936320 140247040 290324480 296222720 ⟨⟨167118135924, 167118135933⟩, ⟨161281469655, 173052188566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 140247040 141557760 290324480 296222720 ⟨⟨165831809772, 165831809775⟩, ⟨160035316509, 171724763374⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 141557760 272629760 296222720 t = true :=
  ⟨_, (join_sr (m := 284426240) (by decide) (join_su (m := 138936320) (by decide) (join_sr (m := 278528000) (by decide) (join_su (m := 137625600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 137625600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 278528000) (by decide) (join_su (m := 140247040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 140247040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 138936320) (by decide) (join_sr (m := 290324480) (by decide) (join_su (m := 137625600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 137625600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 290324480) (by decide) (join_su (m := 140247040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 140247040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (27/160 : ℝ) →
    rho ∈ Set.Icc (13/40 : ℝ) (113/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e2 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  have e3 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
