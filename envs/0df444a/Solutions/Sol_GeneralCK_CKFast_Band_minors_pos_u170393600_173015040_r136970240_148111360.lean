-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u170393600_173015040_r136970240_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:15:07.669846+00:00
-- url     : https://prove2.me/submissions/e01cec59-0f5f-4daa-b443-13becfd18fd9

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/64, 33/160]`, `ρ ∈ [209/1280, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 170393600 171048960 136970240 139755520 ⟨⟨69448636646, 69448636654⟩, ⟨67249087998, 71668111160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 171048960 171704320 136970240 139755520 ⟨⟨69152882342, 69152882349⟩, ⟨66960446648, 71365134883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 171048960 139755520 142540800 ⟨⟨70768292112, 70768292119⟩, ⟨68563571014, 72992923682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 171048960 171704320 139755520 142540800 ⟨⟨70467503523, 70467503529⟩, ⟨68269909010, 72684900013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 171704320 172359680 136970240 139755520 ⟨⟨68858465195, 68858465198⟩, ⟨66673097447, 71063541726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 172359680 173015040 136970240 139755520 ⟨⟨68565373047, 68565373053⟩, ⟨66387028685, 70763319076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 171704320 172359680 139755520 142540800 ⟨⟨70168068378, 70168068381⟩, ⟨67977555459, 72378275725⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 172359680 173015040 139755520 142540800 ⟨⟨69869974414, 69869974421⟩, ⟨67686498547, 72073038099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 170393600 171048960 142540800 145326080 ⟨⟨72085224198, 72085224204⟩, ⟨69875352040, 74314991276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 171048960 171704320 142540800 145326080 ⟨⟨71779431636, 71779431644⟩, ⟨69576699375, 74001950849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 170393600 171048960 145326080 148111360 ⟨⟨73399451973, 73399451981⟩, ⟨71184449950, 75634333207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 171048960 171704320 145326080 148111360 ⟨⟨73088685461, 73088685467⟩, ⟨70880836329, 75316306357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 171704320 172359680 142540800 145326080 ⟨⟨71475008489, 71475008493⟩, ⟨69279371154, 73690325739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 172359680 173015040 142540800 145326080 ⟨⟨71171942385, 71171942391⟩, ⟨68983355457, 73380103127⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 171704320 172359680 145326080 148111360 ⟨⟨72779304015, 72779304018⟩, ⟨70578562829, 74999710444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 172359680 173015040 145326080 148111360 ⟨⟨72471295163, 72471295171⟩, ⟨70277617432, 74684532544⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 170393600 173015040 136970240 148111360 t = true :=
  ⟨_, (join_sr (m := 142540800) (by decide) (join_su (m := 171704320) (by decide) (join_sr (m := 139755520) (by decide) (join_su (m := 171048960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 171048960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 139755520) (by decide) (join_su (m := 172359680) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 172359680) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 171704320) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 171048960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 171048960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 145326080) (by decide) (join_su (m := 172359680) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 172359680) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/64 : ℝ) (33/160 : ℝ) →
    rho ∈ Set.Icc (209/1280 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e1 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e2 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
