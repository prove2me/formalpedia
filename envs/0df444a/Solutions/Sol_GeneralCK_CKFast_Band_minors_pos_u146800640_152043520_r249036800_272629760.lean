-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u146800640_152043520_r249036800_272629760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:55:03.690898+00:00
-- url     : https://prove2.me/submissions/aa2a8a5c-5303-40e8-bc2b-a38329f902a2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/40, 29/160]`, `ρ ∈ [19/64, 13/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 146800640 148111360 249036800 254935040 ⟨⟨139557187657, 139557187661⟩, ⟨134083799821, 145125538528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 148111360 149422080 249036800 254935040 ⟨⟨138453165682, 138453165691⟩, ⟨133017391274, 143982945334⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 146800640 148111360 254935040 260833280 ⟨⟨142452508755, 142452508759⟩, ⟨136960036936, 148039527759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 148111360 149422080 254935040 260833280 ⟨⟨141330646616, 141330646626⟩, ⟨135875764676, 146879133707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 149422080 150732800 249036800 254935040 ⟨⟨137358668300, 137358668309⟩, ⟨131960038134, 142850360869⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 150732800 152043520 249036800 254935040 ⟨⟨136273530869, 136273530876⟩, ⟨130911584778, 141727611163⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 149422080 150732800 254935040 260833280 ⟨⟨140218360938, 140218360946⟩, ⟨134800603838, 145728795649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 150732800 152043520 254935040 260833280 ⟨⟨139115487343, 139115487350⟩, ⟨133734398912, 144588340056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 146800640 148111360 260833280 266731520 ⟨⟨145334861052, 145334861055⟩, ⟨139823510946, 150940341175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 148111360 149422080 260833280 266731520 ⟨⟨144195406081, 144195406088⟩, ⟨138721617841, 149762397971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 146800640 148111360 266731520 272629760 ⟨⟨148204455263, 148204455267⟩, ⟨142674427938, 153828194174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 148111360 149422080 266731520 272629760 ⟨⟨147047649187, 147047649194⟩, ⟨141555151407, 152632947766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 149422080 150732800 260833280 266731520 ⟨⟨143065575243, 143065575251⟩, ⟨137628888039, 148594553790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 150732800 152043520 260833280 266731520 ⟨⟨141945204498, 141945204505⟩, ⟨136545166208, 147436635592⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 149422080 150732800 266731520 272629760 ⟨⟨145900510871, 145900510880⟩, ⟨140445086065, 151447839312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 150732800 152043520 266731520 272629760 ⟨⟨144762876671, 144762876680⟩, ⟨139344076827, 150272696336⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 146800640 152043520 249036800 272629760 t = true :=
  ⟨_, (join_sr (m := 260833280) (by decide) (join_su (m := 149422080) (by decide) (join_sr (m := 254935040) (by decide) (join_su (m := 148111360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 148111360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 254935040) (by decide) (join_su (m := 150732800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 150732800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 149422080) (by decide) (join_sr (m := 266731520) (by decide) (join_su (m := 148111360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 148111360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 266731520) (by decide) (join_su (m := 150732800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 150732800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/40 : ℝ) (29/160 : ℝ) →
    rho ∈ Set.Icc (19/64 : ℝ) (13/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e1 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e2 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e3 : (((272629760 : ℤ) : ℝ) / (D : ℝ)) = (13/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
