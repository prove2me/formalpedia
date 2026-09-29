-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_110100480_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:21:13.474585+00:00
-- url     : https://prove2.me/submissions/89df6e09-ab75-4629-91dc-7f0ba1c8b2fd

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 21/160]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 106168320 142868480 145817600 ⟨⟨112637837560, 112637837568⟩, ⟨107427011347, 117947391027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 106168320 145817600 148766720 ⟨⟨114655385841, 114655385849⟩, ⟨109433413680, 119975714106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 106168320 107479040 142868480 145817600 ⟨⟨111553539343, 111553539353⟩, ⟨106389054897, 116815264180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 106168320 107479040 145817600 148766720 ⟨⟨113556062993, 113556063004⟩, ⟨108380407703, 118828603237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 106168320 148766720 151715840 ⟨⟨116663908997, 116663909008⟩, ⟨111430932549, 121994870610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 106168320 151715840 154664960 ⟨⟨118663515815, 118663515823⟩, ⟨113419674097, 124004971993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 106168320 107479040 148766720 151715840 ⟨⟨115549761861, 115549761869⟩, ⟨110363073868, 120832979480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 106168320 107479040 151715840 154664960 ⟨⟨117534741121, 117534741129⟩, ⟨112337156032, 122828500653⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 107479040 108789760 142868480 145817600 ⟨⟨110484975454, 110484975460⟩, ⟨105365934604, 115699806986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 108789760 145817600 148766720 ⟨⟨112472590954, 112472590960⟩, ⟨107342358811, 117698273414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 108789760 110100480 142868480 145817600 ⟨⟨109431747980, 109431747990⟩, ⟨104357278576, 114600594265⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 108789760 110100480 145817600 148766720 ⟨⟨111404570921, 111404570929⟩, ⟨106318893970, 116584298848⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 107479040 108789760 148766720 151715840 ⟨⟨114451577270, 114451577277⟩, ⟨109310288532, 119687975987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 107479040 108789760 151715840 154664960 ⟨⟨116422036107, 116422036110⟩, ⟨111269823037, 121669018868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 108789760 110100480 148766720 151715840 ⟨⟨113368955665, 113368955674⟩, ⟨108272202497, 118559433858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 108789760 110100480 151715840 154664960 ⟨⟨115325000568, 115325000576⟩, ⟨110217300176, 120526100010⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 110100480 142868480 154664960 t = true :=
  ⟨_, (join_su (m := 107479040) (by decide) (join_sr (m := 148766720) (by decide) (join_su (m := 106168320) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 145817600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 106168320) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 151715840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 148766720) (by decide) (join_su (m := 108789760) (by decide) (join_sr (m := 145817600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 145817600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 108789760) (by decide) (join_sr (m := 151715840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 151715840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
