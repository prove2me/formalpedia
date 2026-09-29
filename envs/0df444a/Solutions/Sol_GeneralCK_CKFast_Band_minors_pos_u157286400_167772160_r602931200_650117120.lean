-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r602931200_650117120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:12:24.927817+00:00
-- url     : https://prove2.me/submissions/cb601dc6-370a-4f68-9c81-5f787183c961

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [23/32, 31/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 602931200 614727680 ⟨⟨281529519090, 281529519101⟩, ⟨269371099788, 293955408585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 162529280 602931200 614727680 ⟨⟨277911917035, 277911917046⟩, ⟨265872994675, 290216863573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 159907840 614727680 626524160 ⟨⟨286141838592, 286141838603⟩, ⟨273930187389, 298617961745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 614727680 626524160 ⟨⟨282484582537, 282484582547⟩, ⟨270391653583, 294840686991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 165150720 602931200 614727680 ⟨⟨274324447788, 274324447793⟩, ⟨262403541818, 286509909013⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 167772160 602931200 614727680 ⟨⟨270766395615, 270766395625⟩, ⟨258962056199, 282833800278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 162529280 165150720 614727680 626524160 ⟨⟨278857109894, 278857109899⟩, ⟨266881473799, 291094597899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165150720 167772160 614727680 626524160 ⟨⟨275258718459, 275258718470⟩, ⟨263398974824, 287378965189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 159907840 626524160 638320640 ⟨⟨290737353415, 290737353425⟩, ⟨278472858631, 303263302154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159907840 162529280 626524160 638320640 ⟨⟨287040922312, 287040922322⟩, ⟨274894365864, 299447784568⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 159907840 638320640 650117120 ⟨⟨295316638673, 295316638684⟩, ⟨282999671960, 307892021264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 159907840 162529280 638320640 650117120 ⟨⟨291581491023, 291581491033⟩, ⟨279381670149, 304038726695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 162529280 165150720 626524160 638320640 ⟨⟨283373918004, 283373918008⟩, ⟨271343921179, 295663041259⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 167772160 626524160 638320640 ⟨⟨279735651672, 279735651683⟩, ⟨267820863087, 291908358080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 162529280 165150720 638320640 650117120 ⟨⟨287875406877, 287875406883⟩, ⟨275791403321, 300215788976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 165150720 167772160 638320640 650117120 ⟨⟨284197710655, 284197710667⟩, ⟨272228221616, 296422508878⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 602931200 650117120 t = true :=
  ⟨_, (join_sr (m := 626524160) (by decide) (join_su (m := 162529280) (by decide) (join_sr (m := 614727680) (by decide) (join_su (m := 159907840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 159907840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 614727680) (by decide) (join_su (m := 165150720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 165150720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 162529280) (by decide) (join_sr (m := 638320640) (by decide) (join_su (m := 159907840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 159907840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 638320640) (by decide) (join_su (m := 165150720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 165150720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (23/32 : ℝ) (31/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  have e3 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
