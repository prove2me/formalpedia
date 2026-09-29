-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u218890240_220200960_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:21:44.781764+00:00
-- url     : https://prove2.me/submissions/1596440d-9fe8-46af-ad7f-02559a416073

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [167/640, 21/80]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 218890240 219217920 125829120 127221760 ⟨⟨46374082077, 46374082082⟩, ⟨45495073726, 47256550483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 219217920 219545600 125829120 127221760 ⟨⟨46271466774, 46271466779⟩, ⟨45393625675, 47152760226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 218890240 219217920 127221760 128614400 ⟨⟨46869703061, 46869703068⟩, ⟨45989642753, 47753224369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 219217920 219545600 127221760 128614400 ⟨⟨46766051332, 46766051338⟩, ⟨45887159940, 47648396028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 219545600 219873280 125829120 127221760 ⟨⟨46169020732, 46169020739⟩, ⟨45292343974, 47049142169⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 219873280 220200960 125829120 127221760 ⟨⟨46066743282, 46066743288⟩, ⟨45191227966, 46945695629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 219545600 219873280 127221760 128614400 ⟨⟨46662570210, 46662570217⟩, ⟨45784844821, 47543741237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 219873280 220200960 127221760 128614400 ⟨⟨46559259022, 46559259029⟩, ⟨45682696736, 47439259309⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 218890240 219217920 128614400 130007040 ⟨⟨47365027203, 47365027208⟩, ⟨46483915704, 48249600635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 219217920 219545600 128614400 130007040 ⟨⟨47260340862, 47260340868⟩, ⟨46380399938, 48143736038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 219217920 130007040 131399680 ⟨⟨47860055274, 47860055279⟩, ⟨46977893352, 48745680062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 219217920 219545600 130007040 131399680 ⟨⟨47754336134, 47754336139⟩, ⟨46873346434, 48638781023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 219545600 219873280 128614400 130007040 ⟨⟨47155826467, 47155826473⟩, ⟨46277053201, 48038046327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 219873280 220200960 128614400 130007040 ⟨⟨47051483338, 47051483344⟩, ⟨46173874827, 47932530814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 219545600 219873280 130007040 131399680 ⟨⟨47648790265, 47648790272⟩, ⟨46768969872, 48532058203⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 219873280 220200960 130007040 131399680 ⟨⟨47543416986, 47543416992⟩, ⟨46664762992, 48425510905⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 218890240 220200960 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 219545600) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 219217920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 219217920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 219873280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 219873280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 219545600) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 219217920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 219217920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 219873280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 219873280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (167/640 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((218890240 : ℤ) : ℝ) / (D : ℝ)) = (167/640 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
