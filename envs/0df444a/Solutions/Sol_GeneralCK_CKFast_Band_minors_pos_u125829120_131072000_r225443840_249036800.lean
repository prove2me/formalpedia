-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_131072000_r225443840_249036800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:42:19.741412+00:00
-- url     : https://prove2.me/submissions/ceb22a0a-24a7-4fd0-bc0b-736f424354d1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 5/32]`, `ρ ∈ [43/160, 19/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 127139840 225443840 231342080 ⟨⟨145735458337, 145735458346⟩, ⟨139663059157, 151923457318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 127139840 128450560 225443840 231342080 ⟨⟨144530957428, 144530957434⟩, ⟨138505530791, 150670631950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 125829120 127139840 231342080 237240320 ⟨⟨148996516768, 148996516776⟩, ⟨142904905020, 155202980204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 127139840 128450560 231342080 237240320 ⟨⟨147772026946, 147772026949⟩, ⟨141727294903, 153930285228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 128450560 129761280 225443840 231342080 ⟨⟨143339001667, 143339001677⟩, ⟨137359866187, 149431057695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 129761280 131072000 225443840 231342080 ⟨⟨142159344948, 142159344958⟩, ⟨136225834303, 148204472771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 128450560 129761280 231342080 237240320 ⟨⟨146560147852, 146560147860⟩, ⟨140561621534, 152670898710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 129761280 131072000 231342080 237240320 ⟨⟨145360634079, 145360634088⟩, ⟨139407654272, 151424559890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 125829120 127139840 237240320 243138560 ⟨⟨152238646610, 152238646620⟩, ⟨146128140670, 158463257286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 127139840 128450560 237240320 243138560 ⟨⟨150994529692, 150994529699⟩, ⟨144930804271, 157171060597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125829120 127139840 243138560 249036800 ⟨⟨155462202943, 155462202953⟩, ⟨149333112216, 161704652682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 127139840 128450560 243138560 249036800 ⟨⟨154198810958, 154198810963⟩, ⟨148116395513, 160393312086⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 128450560 129761280 237240320 243138560 ⟨⟨149763082643, 149763082653⟩, ⟨143745471230, 155892223221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 129761280 131072000 237240320 243138560 ⟨⟨148544060862, 148544060872⟩, ⟨142571911418, 154626485530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 128450560 129761280 243138560 249036800 ⟨⟨152948141812, 152948141822⟩, ⟨146911742665, 159095375451⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 129761280 131072000 243138560 249036800 ⟨⟨151709951818, 151709951828⟩, ⟨145718924162, 157810584383⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 131072000 225443840 249036800 t = true :=
  ⟨_, (join_sr (m := 237240320) (by decide) (join_su (m := 128450560) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 127139840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 127139840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 231342080) (by decide) (join_su (m := 129761280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 129761280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 128450560) (by decide) (join_sr (m := 243138560) (by decide) (join_su (m := 127139840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 127139840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 243138560) (by decide) (join_su (m := 129761280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 129761280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (5/32 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (19/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
