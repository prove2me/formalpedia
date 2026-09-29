-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u183500800_186122240_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T23:27:36.399107+00:00
-- url     : https://prove2.me/submissions/f3486a9e-f928-4b85-affd-e90b476301b8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/32, 71/320]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 183500800 184156160 125829120 127221760 ⟨⟨58556559686, 58556559692⟩, ⟨56875139905, 60249853354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 183500800 184156160 127221760 128614400 ⟨⟨59172511705, 59172511711⟩, ⟨57488861626, 60868036986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 184156160 184811520 125829120 127221760 ⟨⟨58305764950, 58305764956⟩, ⟨56628827198, 59994521529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 184156160 184811520 127221760 128614400 ⟨⟨58919296330, 58919296336⟩, ⟨57240134416, 60610278486⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 183500800 184156160 128614400 130007040 ⟨⟨59787903269, 59787903276⟩, ⟨58102025933, 61485657095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 183500800 184156160 130007040 131399680 ⟨⟨60402736192, 60402736200⟩, ⟨58714634626, 62102715505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 184156160 184811520 128614400 130007040 ⟨⟨59532273654, 59532273662⟩, ⟨57850890569, 61225478370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 184156160 184811520 130007040 131399680 ⟨⟨60144698712, 60144698718⟩, ⟨58461097431, 61840122981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 184811520 185466880 125829120 127221760 ⟨⟨58056025444, 58056025448⟩, ⟨56383541817, 59740273295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 184811520 185466880 127221760 128614400 ⟨⟨58667143919, 58667143922⟩, ⟨56992442258, 60353611318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 185466880 186122240 125829120 127221760 ⟨⟨57807331919, 57807331925⟩, ⟨56139274780, 59487099137⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 185466880 186122240 127221760 128614400 ⟨⟨58416045170, 58416045176⟩, ⟨56745776116, 60098025920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 184811520 185466880 128614400 130007040 ⟨⟨59277714672, 59277714675⟩, ⟨57600797917, 60966398654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 184811520 185466880 130007040 131399680 ⟨⟨59887739462, 59887739467⟩, ⟨58208610539, 61578637071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 185466880 186122240 128614400 130007040 ⟨⟨59024216967, 59024216973⟩, ⟨57351738886, 60708408328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 185466880 186122240 130007040 131399680 ⟨⟨59631849038, 59631849045⟩, ⟨57957164809, 61318248106⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 183500800 186122240 125829120 131399680 t = true :=
  ⟨_, (join_su (m := 184811520) (by decide) (join_sr (m := 128614400) (by decide) (join_su (m := 184156160) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 127221760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 184156160) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 130007040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 128614400) (by decide) (join_su (m := 185466880) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 127221760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 185466880) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 130007040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/32 : ℝ) (71/320 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e1 : (((186122240 : ℤ) : ℝ) / (D : ℝ)) = (71/320 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
