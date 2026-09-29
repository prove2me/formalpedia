-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_191365120_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:26:59.354973+00:00
-- url     : https://prove2.me/submissions/6d6feb4d-0e33-4313-a174-f65fc7123f0a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 73/320]`, `ρ ∈ [3/20, 401/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 189399040 125829120 127221760 ⟨⟨56579237562, 56579237568⟩, ⟨54932907212, 58237013915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 189399040 127221760 128614400 ⟨⟨57176038094, 57176038102⟩, ⟨55527526273, 58835998002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 189399040 190054400 125829120 127221760 ⟨⟨56336631435, 56336631442⟩, ⟨54694567061, 57990090293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 189399040 190054400 127221760 128614400 ⟨⟨56931071740, 56931071747⟩, ⟨55286831951, 58586708182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 189399040 128614400 130007040 ⟨⟨57772327519, 57772327526⟩, ⟨56121636875, 59434468302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 189399040 130007040 131399680 ⟨⟨58368107434, 58368107441⟩, ⟨56715240610, 60032426423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 189399040 190054400 128614400 130007040 ⟨⟨57525006816, 57525006821⟩, ⟨55878594218, 59182818210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 189399040 190054400 130007040 131399680 ⟨⟨58118438236, 58118438241⟩, ⟨56469855423, 59778421959⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 190054400 190709760 125829120 127221760 ⟨⟨56095009370, 56095009376⟩, ⟨54457185079, 57744177045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 190054400 190709760 127221760 128614400 ⟨⟨56687096768, 56687096775⟩, ⟨55047103110, 58338436067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 190709760 191365120 125829120 127221760 ⟨⟨55854362903, 55854362910⟩, ⟨54220753042, 57499265467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 190709760 191365120 127221760 128614400 ⟨⟨56444104664, 56444104671⟩, ⟨54808331472, 58091172902⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 190054400 190709760 128614400 130007040 ⟨⟨57278684753, 57278684758⟩, ⟨55636524287, 58932193090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 190054400 190709760 130007040 131399680 ⟨⟨57869774872, 57869774877⟩, ⟨56225450149, 59525449670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 190709760 191365120 128614400 130007040 ⟨⟨57033352765, 57033352772⟩, ⟨55395418756, 58682584136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 190709760 191365120 130007040 131399680 ⟨⟨57622108732, 57622108739⟩, ⟨55982016413, 59273500702⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 191365120 125829120 131399680 t = true :=
  ⟨_, (join_su (m := 190054400) (by decide) (join_sr (m := 128614400) (by decide) (join_su (m := 189399040) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 127221760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 189399040) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 130007040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 128614400) (by decide) (join_su (m := 190709760) (by decide) (join_sr (m := 127221760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 127221760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 190709760) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 130007040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (73/320 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
