-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_67108864_r499384320_547880960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:21:19.745586+00:00
-- url     : https://prove2.me/submissions/8aad3eaf-e236-4da0-8548-93ca5d5179bf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 2/25]`, `ρ ∈ [381/640, 209/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 54525952 499384320 511508480 ⟨⟨415395647991, 415395647996⟩, ⟨389102175800, 442428027435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50331648 54525952 511508480 523632640 ⟨⟨421612574155, 421612574163⟩, ⟨395388326610, 448543223028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 54525952 58720256 499384320 511508480 ⟨⟨405952831842, 405952831856⟩, ⟨380263712715, 432382106725⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 54525952 58720256 511508480 523632640 ⟨⟨412161528548, 412161528563⟩, ⟨386526554165, 438506068977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 50331648 54525952 523632640 535756800 ⟨⟨427770779909, 427770779919⟩, ⟨401614465355, 454601922402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 50331648 54525952 535756800 547880960 ⟨⟨433873186487, 433873186498⟩, ⟨407783500645, 460607006957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 54525952 58720256 523632640 535756800 ⟨⟨418312402275, 418312402289⟩, ⟨392730700455, 444573902948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 54525952 58720256 535756800 547880960 ⟨⟨424408272433, 424408272448⟩, ⟨398878941712, 450588412566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 58720256 62914560 499384320 511508480 ⟨⟨396831935143, 396831935156⟩, ⟨371718920432, 422684440871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 58720256 62914560 511508480 523632640 ⟨⟨403025929833, 403025929849⟩, ⟨377953219383, 428809364167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 62914560 67108864 499384320 511508480 ⟨⟨388009039409, 388009039424⟩, ⟨363446449991, 413308921595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 62914560 67108864 511508480 523632640 ⟨⟨394182485888, 394182485902⟩, ⟨369647488114, 419427741426⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 58720256 62914560 523632640 535756800 ⟨⟨409163156159, 409163156174⟩, ⟨384130236730, 434878755361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 58720256 62914560 535756800 547880960 ⟨⟨415246327779, 415246327793⟩, ⟨390252643833, 440895332320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 62914560 67108864 523632640 535756800 ⟨⟨400300346907, 400300346920⟩, ⟨375792733521, 425491816227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 62914560 67108864 535756800 547880960 ⟨⟨406365228081, 406365228095⟩, ⟨381884739542, 431503771587⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 67108864 499384320 547880960 t = true :=
  ⟨_, (join_su (m := 58720256) (by decide) (join_sr (m := 523632640) (by decide) (join_su (m := 54525952) (by decide) (join_sr (m := 511508480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 511508480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 54525952) (by decide) (join_sr (m := 535756800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 535756800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 523632640) (by decide) (join_su (m := 62914560) (by decide) (join_sr (m := 511508480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 511508480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 62914560) (by decide) (join_sr (m := 535756800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 535756800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (381/640 : ℝ) (209/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((499384320 : ℤ) : ℝ) / (D : ℝ)) = (381/640 : ℝ) := by norm_num [D]
  have e3 : (((547880960 : ℤ) : ℝ) / (D : ℝ)) = (209/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
