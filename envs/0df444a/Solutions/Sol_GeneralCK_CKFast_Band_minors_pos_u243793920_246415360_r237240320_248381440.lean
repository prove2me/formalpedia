-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u243793920_246415360_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:57:21.29375+00:00
-- url     : https://prove2.me/submissions/01fb4996-7b7f-411d-b915-879f0a403796

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [93/320, 47/160]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 243793920 244449280 237240320 240025600 ⟨⟨72221978562, 72221978565⟩, ⟨70482185943, 73973975283⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 244449280 245104640 237240320 240025600 ⟨⟨71894339738, 71894339745⟩, ⟨70158857431, 73641982547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 243793920 244449280 240025600 242810880 ⟨⟨73034832100, 73034832103⟩, ⟨71291402045, 74790476051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 244449280 245104640 240025600 242810880 ⟨⟨72703762418, 72703762425⟩, ⟨70964651931, 74455043308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 245104640 245760000 237240320 240025600 ⟨⟨71567461931, 71567461937⟩, ⟨69836272202, 73310768804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 245760000 246415360 237240320 240025600 ⟨⟨71241339805, 71241339812⟩, ⟨69514425043, 72980328597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 245104640 245760000 240025600 242810880 ⟨⟨72373458463, 72373458470⟩, ⟨70638649813, 74120394264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 245760000 246415360 240025600 242810880 ⟨⟨72043914880, 72043914885⟩, ⟨70313390458, 73786523439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 244449280 242810880 245596160 ⟨⟨73847081649, 73847081652⟩, ⟨72100015973, 75606370965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 244449280 245104640 242810880 245596160 ⟨⟨73512588732, 73512588739⟩, ⟨71769851817, 75267505900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 243793920 244449280 245596160 248381440 ⟨⟨74658730059, 74658730060⟩, ⟨72908030567, 76421662883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 244449280 245104640 245596160 248381440 ⟨⟨74320821486, 74320821492⟩, ⟨72574459889, 76079373137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 245104640 245760000 242810880 245596160 ⟨⟨73178866179, 73178866185⟩, ⟨71440440300, 74929429163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 245760000 246415360 242810880 245596160 ⟨⟨72845908609, 72845908616⟩, ⟨71111776163, 74592135254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 245760000 245596160 248381440 ⟨⟨73983687839, 73983687845⟩, ⟨72241646415, 75737876275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245760000 246415360 245596160 248381440 ⟨⟨73647323716, 73647323722⟩, ⟨71909584867, 75397166773⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 243793920 246415360 237240320 248381440 t = true :=
  ⟨_, (join_sr (m := 242810880) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 240025600) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 244449280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 240025600) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 245760000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 245104640) (by decide) (join_sr (m := 245596160) (by decide) (join_su (m := 244449280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 244449280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 245596160) (by decide) (join_su (m := 245760000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 245760000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (93/320 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((243793920 : ℤ) : ℝ) / (D : ℝ)) = (93/320 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
