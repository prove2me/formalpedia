-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_220200960_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:18:13.006983+00:00
-- url     : https://prove2.me/submissions/1494d596-5e34-4619-a8a8-2ea65b2d682a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 21/80]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 216268800 248381440 251166720 ⟨⟨91158342856, 91158342863⟩, ⟨87848319174, 94508388140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 214958080 216268800 251166720 253952000 ⟨⟨92121302829, 92121302836⟩, ⟨88803881292, 95478771696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 216268800 217579520 248381440 251166720 ⟨⟨90397173131, 90397173139⟩, ⟨87102155445, 93731950295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 216268800 217579520 251166720 253952000 ⟨⟨91352912780, 91352912787⟩, ⟨88050525312, 94695086436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 214958080 216268800 253952000 256737280 ⟨⟨93083266251, 93083266259⟩, ⟨89758454264, 96448151031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 214958080 216268800 256737280 259522560 ⟨⟨94044238480, 94044238488⟩, ⟨90712043401, 97416531548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 217579520 253952000 256737280 ⟨⟨92307678279, 92307678286⟩, ⟨88997928120, 95657241082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216268800 217579520 256737280 259522560 ⟨⟨93261474836, 93261474842⟩, ⟨89944369032, 96618419475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 217579520 218890240 248381440 251166720 ⟨⟨89640211683, 89640211689⟩, ⟨86360055761, 92959868182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 217579520 218890240 251166720 253952000 ⟨⟨90588752209, 90588752215⟩, ⟨87301254749, 93915777918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 218890240 220200960 248381440 251166720 ⟨⟨88887398579, 88887398582⟩, ⟨85621962293, 92192079714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 218890240 220200960 251166720 253952000 ⟨⟨89828761021, 89828761025⟩, ⟨86556011599, 93140783896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 217579520 218890240 253952000 256737280 ⟨⟨91536340580, 91536340586⟩, ⟨88241508362, 94870728464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 217579520 218890240 256737280 259522560 ⟨⟨92482981854, 92482981860⟩, ⟨89180821619, 95824724916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 218890240 220200960 253952000 256737280 ⟨⟨90769192899, 90769192902⟩, ⟨87489136820, 94088550787⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 218890240 220200960 256737280 259522560 ⟨⟨91708699126, 91708699129⟩, ⟨88421342829, 95035385337⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 220200960 248381440 259522560 t = true :=
  ⟨_, (join_su (m := 217579520) (by decide) (join_sr (m := 253952000) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 251166720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 216268800) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 256737280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 253952000) (by decide) (join_su (m := 218890240) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 251166720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 218890240) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 256737280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
