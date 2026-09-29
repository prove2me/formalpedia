-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_128450560_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:02:19.860306+00:00
-- url     : https://prove2.me/submissions/2ece80c6-79b6-4bf3-980a-643a607cda20

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 49/320]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 126484480 107479040 110428160 ⟨⟨75149021052, 75149021054⟩, ⟨72328189819, 78002678879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 126484480 127139840 107479040 110428160 ⟨⟨74795304481, 74795304488⟩, ⟨71986408577, 77636781079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 126484480 110428160 113377280 ⟨⟨77024613350, 77024613355⟩, ⟨74196736803, 79885222680⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 126484480 127139840 110428160 113377280 ⟨⟨76663305506, 76663305513⟩, ⟨73847379798, 79511720104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 127139840 127795200 107479040 110428160 ⟨⟨74443941324, 74443941331⟩, ⟨71646877881, 77273342469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 127795200 128450560 107479040 110428160 ⟨⟨74094903613, 74094903620⟩, ⟨71309571142, 76912333661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 127139840 127795200 110428160 113377280 ⟨⟨76304387219, 76304387226⟩, ⟨73500309680, 79140712626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 127795200 128450560 110428160 113377280 ⟨⟨75947830231, 75947830240⟩, ⟨73155499557, 78772170579⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 126484480 113377280 116326400 ⟨⟨78892999356, 78892999360⟩, ⟨76058152502, 81760485036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 126484480 127139840 113377280 116326400 ⟨⟨78524184031, 78524184038⟩, ⟨75701302449, 81379462550⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 126484480 116326400 119275520 ⟨⟨80754255178, 80754255182⟩, ⟨77912511834, 83628543262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 126484480 127139840 116326400 119275520 ⟨⟨80378014869, 80378014877⟩, ⟨77548250176, 83240084410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 127139840 127795200 113377280 116326400 ⟨⟨78157793367, 78157793375⟩, ⟨75346774598, 81000970018⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 127795200 128450560 113377280 116326400 ⟨⟨77793798831, 77793798840⟩, ⟨74994541770, 80624977505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 127139840 127795200 116326400 119275520 ⟨⟨80004233313, 80004233320⟩, ⟨77186345033, 82854189342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 127795200 128450560 116326400 119275520 ⟨⟨79632881709, 79632881716⟩, ⟨76826768954, 82470827862⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 128450560 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 127139840) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 126484480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 126484480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 127795200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 127795200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 127139840) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 126484480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 126484480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 127795200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 127795200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (49/320 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((128450560 : ℤ) : ℝ) / (D : ℝ)) = (49/320 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
