-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u152043520_157286400_r213647360_225443840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:49:25.507719+00:00
-- url     : https://prove2.me/submissions/fb2acd4b-801f-448d-b6dc-0c0850f256e3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [29/160, 3/16]`, `ρ ∈ [163/640, 43/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 152043520 153354240 213647360 216596480 ⟨⟨117261621925, 117261621932⟩, ⟨113057519349, 121526067649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 152043520 153354240 216596480 219545600 ⟨⟨118715196943, 118715196951⟩, ⟨114501809289, 122988851106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 153354240 154664960 213647360 216596480 ⟨⟨116310486186, 116310486190⟩, ⟨112132372298, 120548366714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 153354240 154664960 216596480 219545600 ⟨⟨117754429014, 117754429018⟩, ⟨113567042745, 122001509393⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 152043520 153354240 219545600 222494720 ⟨⟨120165428202, 120165428211⟩, ⟨115942797291, 124448248439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 152043520 153354240 222494720 225443840 ⟨⟨121612342582, 121612342591⟩, ⟨117380509799, 125904286969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 153354240 154664960 219545600 222494720 ⟨⟨119195095220, 119195095224⟩, ⟨114998477351, 123451334120⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 153354240 154664960 222494720 225443840 ⟨⟨120632510927, 120632510931⟩, ⟨116426701821, 124897867445⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 154664960 155975680 213647360 216596480 ⟨⟨115367810720, 115367810728⟩, ⟨111215343535, 119579477599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 154664960 155975680 216596480 219545600 ⟨⟨116802162283, 116802162292⟩, ⟨112640436521, 121023019190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 155975680 157286400 213647360 216596480 ⟨⟨114433445905, 114433445914⟩, ⟨110306290176, 118619243715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 155975680 157286400 216596480 219545600 ⟨⟨115858246938, 115858246947⟩, ⟨111721847500, 120053223774⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 154664960 155975680 219545600 222494720 ⟨⟨118233303118, 118233303125⟩, ⟨114062358540, 122463309745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 154664960 155975680 222494720 225443840 ⟨⟨119661258616, 119661258625⟩, ⟨115481134585, 123900375063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 155975680 157286400 219545600 222494720 ⟨⟨117279901922, 117279901931⟩, ⟨113134297535, 121484018478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 155975680 157286400 222494720 225443840 ⟨⟨118698435539, 118698435548⟩, ⟨114543664573, 122911652902⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 152043520 157286400 213647360 225443840 t = true :=
  ⟨_, (join_su (m := 154664960) (by decide) (join_sr (m := 219545600) (by decide) (join_su (m := 153354240) (by decide) (join_sr (m := 216596480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 216596480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 153354240) (by decide) (join_sr (m := 222494720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 222494720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 219545600) (by decide) (join_su (m := 155975680) (by decide) (join_sr (m := 216596480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 216596480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 155975680) (by decide) (join_sr (m := 222494720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 222494720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (29/160 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (163/640 : ℝ) (43/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((152043520 : ℤ) : ℝ) / (D : ℝ)) = (29/160 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  have e3 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
