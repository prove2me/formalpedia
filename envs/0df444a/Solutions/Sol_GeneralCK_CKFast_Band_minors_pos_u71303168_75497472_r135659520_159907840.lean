-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u71303168_75497472_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:44:53.087895+00:00
-- url     : https://prove2.me/submissions/3e3fb886-8452-4e4b-954a-317eec9d6035

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/200, 9/100]`, `ρ ∈ [207/1280, 61/320]` by 18 cells of the computing
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
theorem cell0 : cellOK 71303168 72351744 135659520 141721600 ⟨⟨142845464881, 142845464891⟩, ⟨134868893979, 151035748665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 72351744 73400320 135659520 141721600 ⟨⟨141521588830, 141521588843⟩, ⟨133628242525, 149624932438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 71303168 72351744 141721600 147783680 ⟨⟨147918211172, 147918211185⟩, ⟨139929399422, 156117024045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 72351744 73400320 141721600 147783680 ⟨⟨146563764776, 146563764787⟩, ⟨138657517220, 154676428062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 73400320 74448896 135659520 138690560 ⟨⟨138955438287, 138955438300⟩, ⟨133158958817, 144866948728⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 73400320 74448896 138690560 141721600 ⟨⟨141478537763, 141478537776⟩, ⟨135674946497, 147396292231⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 74448896 75497472 135659520 138690560 ⟨⟨137681658313, 137681658323⟩, ⟨131942067515, 143534390216⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 74448896 75497472 138690560 141721600 ⟨⟨140189293857, 140189293867⟩, ⟨134442395809, 146048496446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 73400320 74448896 141721600 147783680 ⟨⟨145230917234, 145230917244⟩, ⟨137405551286, 153259207400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 74448896 75497472 141721600 147783680 ⟨⟨143919092413, 143919092425⟩, ⟨136172977033, 151864731094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 71303168 72351744 147783680 153845760 ⟨⟨152921039021, 152921039034⟩, ⟨144921284650, 161127152949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 72351744 73400320 147783680 153845760 ⟨⟨151537342821, 151537342831⟩, ⟨143619473107, 159658112657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 71303168 72351744 153845760 159907840 ⟨⟨157856312532, 157856312542⟩, ⟨149846829578, 166068582544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 72351744 73400320 153845760 159907840 ⟨⟨156444617517, 156444617530⟩, ⟨148516323251, 164572361274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 73400320 74448896 147783680 153845760 ⟨⟨150175365850, 150175365860⟩, ⟨142337733885, 158212527372⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 74448896 75497472 147783680 153845760 ⟨⟨148834536340, 148834536353⟩, ⟨141075544996, 156789772493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 73400320 74448896 153845760 159907840 ⟨⟨155054737052, 155054737064⟩, ⟨147206019984, 163099650136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 74448896 75497472 153845760 159907840 ⟨⟨153686104248, 153686104261⟩, ⟨145915400959, 161649831340⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 71303168 75497472 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 73400320) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 72351744) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 72351744) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 74448896) (by decide) (join_sr (m := 138690560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 138690560) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 74448896) (by decide) (leaf_ok cell8) (leaf_ok cell9)))) (join_su (m := 73400320) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 72351744) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 72351744) (by decide) (leaf_ok cell12) (leaf_ok cell13))) (join_sr (m := 153845760) (by decide) (join_su (m := 74448896) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_su (m := 74448896) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/200 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
