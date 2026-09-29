-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u213647360_214958080_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:12:49.886089+00:00
-- url     : https://prove2.me/submissions/fe1ae4ed-70e7-4b90-8a6e-e5429635500a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [163/640, 41/160]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 213647360 213975040 125829120 127221760 ⟨⟨48039506024, 48039506027⟩, ⟨47141416063, 48941183180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 213975040 214302720 125829120 127221760 ⟨⟨47934088717, 47934088724⟩, ⟨47037214224, 48834542244⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 213647360 213975040 127221760 128614400 ⟨⟨48551896710, 48551896712⟩, ⟨47652727865, 49454653529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 213975040 214302720 127221760 128614400 ⟨⟨48445420806, 48445420812⟩, ⟨47547469125, 49346952307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214302720 214630400 125829120 127221760 ⟨⟨47828851846, 47828851851⟩, ⟨46933189711, 48728084876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214630400 214958080 125829120 127221760 ⟨⟨47723794683, 47723794688⟩, ⟨46829341811, 48621810343⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 214302720 214630400 127221760 128614400 ⟨⟨48339126757, 48339126763⟩, ⟨47442389132, 49239436076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 214630400 214958080 127221760 128614400 ⟨⟨48233013833, 48233013838⟩, ⟨47337487166, 49132104098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 213647360 213975040 128614400 130007040 ⟨⟨49063960147, 49063960150⟩, ⟨48163713324, 49967795717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 213975040 214302720 128614400 130007040 ⟨⟨48956427622, 48956427629⟩, ⟨48057399654, 49859036196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 213647360 213975040 130007040 131399680 ⟨⟨49575697218, 49575697221⟩, ⟨48674373320, 50480610629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 213975040 214302720 130007040 131399680 ⟨⟨49467110042, 49467110047⟩, ⟨48567006679, 50370794787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214302720 214630400 128614400 130007040 ⟨⟨48849078363, 48849078368⟩, ⟨47951266138, 49750463077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214630400 214958080 128614400 130007040 ⟨⟨48741911633, 48741911638⟩, ⟨47845312051, 49642075620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 214302720 214630400 130007040 131399680 ⟨⟨49358707529, 49358707536⟩, ⟨48459821589, 50261166749⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 214630400 214958080 130007040 131399680 ⟨⟨49250488944, 49250488950⟩, ⟨48352817323, 50151725769⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 213647360 214958080 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 214302720) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 213975040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 213975040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 127221760) (by decide) (join_su (m := 214630400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 214630400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 214302720) (by decide) (join_sr (m := 130007040) (by decide) (join_su (m := 213975040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 213975040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 130007040) (by decide) (join_su (m := 214630400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 214630400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (163/640 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((213647360 : ℤ) : ℝ) / (D : ℝ)) = (163/640 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
