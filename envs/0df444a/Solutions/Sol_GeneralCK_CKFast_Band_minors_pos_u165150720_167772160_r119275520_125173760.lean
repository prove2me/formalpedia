-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u165150720_167772160_r119275520_125173760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:31:29.059401+00:00
-- url     : https://prove2.me/submissions/9e09f478-96d2-48e4-8132-68944bae9f05

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [63/320, 1/5]`, `ρ ∈ [91/640, 191/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 165150720 165806080 119275520 120750080 ⟨⟨62824814907, 62824814909⟩, ⟨60992291929, 64671370090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 165150720 165806080 120750080 122224640 ⟨⟨63556165310, 63556165314⟩, ⟨61721053875, 65405306270⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 165806080 166461440 119275520 120750080 ⟨⟨62552809189, 62552809195⟩, ⟨60725761070, 64393815732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 165806080 166461440 120750080 122224640 ⟨⟨63281299180, 63281299186⟩, ⟨61451669690, 65124884589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 165150720 165806080 122224640 123699200 ⟨⟨64286636814, 64286636818⟩, ⟨62448942481, 66138357948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 165806080 123699200 125173760 ⟨⟨65016232836, 65016232840⟩, ⟨63175961136, 66870528570⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165806080 166461440 122224640 123699200 ⟨⟨64008920216, 64008920224⟩, ⟨62176714831, 65855078976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165806080 166461440 123699200 125173760 ⟨⟨64735675663, 64735675669⟩, ⟨62900899828, 66584402284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 166461440 167116800 119275520 120750080 ⟨⟨62282120975, 62282120981⟩, ⟨60460510166, 64117617099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 166461440 167116800 120750080 122224640 ⟨⟨63007760988, 63007760995⟩, ⟨61183575896, 64845829070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 167116800 167772160 119275520 120750080 ⟨⟨62012737737, 62012737743⟩, ⟨60196527087, 63842761267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 167116800 167772160 120750080 122224640 ⟨⟨62735538133, 62735538140⟩, ⟨60916760279, 64568126714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 166461440 167116800 122224640 123699200 ⟨⟨63732541883, 63732541891⟩, ⟨61905787896, 65573176492⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 166461440 167116800 123699200 125173760 ⟨⟨64456466971, 64456466979⟩, ⟨62627149451, 66299662703⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 167116800 167772160 122224640 123699200 ⟨⟨63457489140, 63457489148⟩, ⟨61636149387, 65292637423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 167116800 167772160 123699200 125173760 ⟨⟨64178594016, 64178594022⟩, ⟨62354697645, 66016296680⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 165150720 167772160 119275520 125173760 t = true :=
  ⟨_, (join_su (m := 166461440) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 165806080) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 120750080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 165806080) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 123699200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 122224640) (by decide) (join_su (m := 167116800) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 120750080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 167116800) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 123699200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (63/320 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (191/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
