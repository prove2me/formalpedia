-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r593756160_616038400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:53:32.773399+00:00
-- url     : https://prove2.me/submissions/b3eaf680-d715-452d-9b60-568cdefc4829

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [453/640, 47/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 593756160 599326720 ⟨⟨210244979203, 210244979212⟩, ⟨201796570878, 218859545647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 212336640 599326720 604897280 ⟨⟨212028900791, 212028900800⟩, ⟨203553446493, 220670405641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 214958080 593756160 599326720 ⟨⟨207161314598, 207161314608⟩, ⟨198780240994, 215707702662⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 599326720 604897280 ⟨⟨208923973103, 208923973111⟩, ⟨200515852966, 217497325126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 212336640 604897280 610467840 ⟨⟨213810791425, 213810791434⟩, ⟨205308318788, 222479202308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 212336640 610467840 616038400 ⟨⟨215590679247, 215590679256⟩, ⟨207061215399, 224285964279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 214958080 604897280 610467840 ⟨⟨210684676603, 210684676612⟩, ⟨202249535292, 219284962586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212336640 214958080 610467840 616038400 ⟨⟨212443452023, 212443452032⟩, ⟨203981314418, 221070642425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 593756160 599326720 ⟨⟨204096815763, 204096815767⟩, ⟨195782338337, 212575763946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 217579520 599326720 604897280 ⟨⟨205838140975, 205838140978⟩, ⟨197496626182, 214344068187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 593756160 599326720 ⟨⟨201051054688, 201051054695⟩, ⟨192802449189, 209463287497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 220200960 599326720 604897280 ⟨⟨202770979260, 202770979269⟩, ⟨194495354987, 211210196003⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214958080 217579520 604897280 610467840 ⟨⟨207577585265, 207577585269⟩, ⟨199209056225, 216110463843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214958080 217579520 610467840 616038400 ⟨⟨209315174377, 209315174381⟩, ⟨200919653764, 217874977088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 220200960 604897280 610467840 ⟨⟨204489095139, 204489095148⟩, ⟨196186473012, 212955270451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217579520 220200960 610467840 616038400 ⟨⟨206205426930, 206205426939⟩, ⟨197875827454, 214698535854⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 593756160 616038400 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 604897280) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 599326720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 599326720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212336640) (by decide) (join_sr (m := 610467840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 610467840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 604897280) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 599326720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 599326720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 217579520) (by decide) (join_sr (m := 610467840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 610467840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (453/640 : ℝ) (47/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  have e3 : (((616038400 : ℤ) : ℝ) / (D : ℝ)) = (47/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
