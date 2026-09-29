-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u196608000_199229440_r131399680_136970240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:27:50.083922+00:00
-- url     : https://prove2.me/submissions/cfb5ab4f-f225-4ffd-a606-ac56bbe17c88

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [15/64, 19/80]`, `ρ ∈ [401/2560, 209/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 196608000 197263360 131399680 132792320 ⟨⟨56004233006, 56004233013⟩, ⟨54399011016, 57620321620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 196608000 197263360 132792320 134184960 ⟨⟨56571412895, 56571412901⟩, ⟨54964089900, 58189605469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 197263360 197918720 131399680 132792320 ⟨⟨55763825093, 55763825100⟩, ⟨54162596861, 57375873477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 197263360 197918720 132792320 134184960 ⟨⟨56328749945, 56328749950⟩, ⟨54725426472, 57942896599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 196608000 197263360 134184960 135577600 ⟨⟨57138153523, 57138153529⟩, ⟨55528731634, 58758447924⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 196608000 197263360 135577600 136970240 ⟨⟨57704456196, 57704456203⟩, ⟨56092937519, 59326850298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 197263360 197918720 134184960 135577600 ⟨⟨56893240627, 56893240633⟩, ⟨55287823988, 58509483457⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 197263360 197918720 135577600 136970240 ⟨⟨57457298428, 57457298435⟩, ⟨55849790688, 59075635345⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 197918720 198574080 131399680 132792320 ⟨⟨55524332104, 55524332106⟩, ⟨53927074355, 57132363894⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 197918720 198574080 132792320 134184960 ⟨⟨56087008442, 56087008446⟩, ⟨54487661208, 57697132822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 198574080 199229440 131399680 132792320 ⟨⟨55285746407, 55285746414⟩, ⟨53692436078, 56889785036⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 198574080 199229440 132792320 134184960 ⟨⟨55846180718, 55846180724⟩, ⟨54250786647, 57452306263⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 197918720 198574080 134184960 135577600 ⟨⟨56649255653, 56649255658⟩, ⟨55047820969, 58261470565⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 197918720 198574080 135577600 136970240 ⟨⟨57211075003, 57211075007⟩, ⟨55607554895, 58825378395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 198574080 199229440 134184960 135577600 ⟨⟨56406190887, 56406190894⟩, ⟨54808715072, 58014401330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 198574080 199229440 135577600 136970240 ⟨⟨56965778163, 56965778170⟩, ⟨55366222592, 58576071490⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 196608000 199229440 131399680 136970240 t = true :=
  ⟨_, (join_su (m := 197918720) (by decide) (join_sr (m := 134184960) (by decide) (join_su (m := 197263360) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 132792320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 197263360) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 135577600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 134184960) (by decide) (join_su (m := 198574080) (by decide) (join_sr (m := 132792320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 132792320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 198574080) (by decide) (join_sr (m := 135577600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 135577600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (15/64 : ℝ) (19/80 : ℝ) →
    rho ∈ Set.Icc (401/2560 : ℝ) (209/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((196608000 : ℤ) : ℝ) / (D : ℝ)) = (15/64 : ℝ) := by norm_num [D]
  have e1 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e2 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  have e3 : (((136970240 : ℤ) : ℝ) / (D : ℝ)) = (209/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
