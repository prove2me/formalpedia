-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r697303040_744488960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:14:13.324152+00:00
-- url     : https://prove2.me/submissions/e6433c12-5bb1-4b30-8bca-1ba82acf8a09

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [133/160, 71/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 697303040 709099520 ⟨⟨317988946689, 317988946701⟩, ⟨305414645296, 330806158674⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 162529280 697303040 709099520 ⟨⟨314066422053, 314066422064⟩, ⟨301605195475, 326770276148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 159907840 709099520 720896000 ⟨⟨322482300064, 322482300077⟩, ⟨309857432932, 335346910639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 709099520 720896000 ⟨⟨318523414931, 318523414942⟩, ⟨306010790339, 331275640262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 165150720 697303040 709099520 ⟨⟨310171061624, 310171061629⟩, ⟨297821824756, 322762589989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 165150720 167772160 697303040 709099520 ⟨⟨306302253542, 306302253553⟩, ⟨294063939741, 318782472232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 162529280 165150720 709099520 720896000 ⟨⟨314591300651, 314591300657⟩, ⟨302189880651, 327232122561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165150720 167772160 709099520 720896000 ⟨⟨310685357594, 310685357605⟩, ⟨298394121386, 323215743141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 159907840 720896000 732692480 ⟨⟨326963142800, 326963142811⟩, ⟨314287977605, 339874861091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159907840 162529280 720896000 732692480 ⟨⟨322968229195, 322968229206⟩, ⟨310404469341, 335768538823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 159907840 732692480 744488960 ⟨⟨331431967330, 331431967342⟩, ⟨318706758466, 344390515193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 159907840 162529280 732692480 744488960 ⟨⟨327401341283, 327401341294⟩, ⟨314786696053, 340249460613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 162529280 165150720 720896000 732692480 ⟨⟨318999689512, 318999689517⟩, ⟨306546343687, 331689522588⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 167772160 720896000 732692480 ⟨⟨315056936165, 315056936178⟩, ⟨302713028952, 327637211331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 162529280 165150720 732692480 744488960 ⟨⟨323396688993, 323396688999⟩, ⟨310891662213, 336135262815⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 165150720 167772160 732692480 744488960 ⟨⟨319417434746, 319417434758⟩, ⟨307021095907, 332047333856⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 697303040 744488960 t = true :=
  ⟨_, (join_sr (m := 720896000) (by decide) (join_su (m := 162529280) (by decide) (join_sr (m := 709099520) (by decide) (join_su (m := 159907840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 159907840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 709099520) (by decide) (join_su (m := 165150720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 165150720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 162529280) (by decide) (join_sr (m := 732692480) (by decide) (join_su (m := 159907840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 159907840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 732692480) (by decide) (join_su (m := 165150720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 165150720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (133/160 : ℝ) (71/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((697303040 : ℤ) : ℝ) / (D : ℝ)) = (133/160 : ℝ) := by norm_num [D]
  have e3 : (((744488960 : ℤ) : ℝ) / (D : ℝ)) = (71/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
