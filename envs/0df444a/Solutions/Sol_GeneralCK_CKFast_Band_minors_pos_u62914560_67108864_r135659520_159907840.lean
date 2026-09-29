-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u62914560_67108864_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:13:28.502298+00:00
-- url     : https://prove2.me/submissions/ee6dc4f9-af69-46cc-8cf9-07fe8e13ac24

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/40, 2/25]`, `ρ ∈ [207/1280, 61/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 62914560 63963136 135659520 141721600 ⟨⟨154286226819, 154286226833⟩, ⟨145574775973, 163245170580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 63963136 65011712 135659520 141721600 ⟨⟨152766930294, 152766930308⟩, ⟨144154675576, 161622019089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 62914560 63963136 141721600 147783680 ⟨⟨159608243581, 159608243595⟩, ⟨150891380960, 168567620198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 63963136 65011712 141721600 147783680 ⟨⟨158057389773, 158057389784⟩, ⟨149438696626, 166914121608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 65011712 66060288 135659520 141721600 ⟨⟨151274631931, 151274631936⟩, ⟨142759333926, 160028239625⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 66060288 67108864 135659520 141721600 ⟨⟨149808537468, 149808537482⟩, ⟨141388032490, 158462957031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 65011712 66060288 141721600 147783680 ⟨⟨156533633073, 156533633078⟩, ⟨148010924820, 165290031218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 66060288 67108864 141721600 147783680 ⟨⟨155036187538, 155036187552⟩, ⟨146607352420, 163694485499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 62914560 63963136 147783680 153845760 ⟨⟨164848718628, 164848718642⟩, ⟨156127882108, 173807205819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 63963136 65011712 147783680 153845760 ⟨⟨163267869334, 163267869346⟩, ⟨154644160194, 172124930352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 62914560 63963136 153845760 159907840 ⟨⟨170010665870, 170010665880⟩, ⟨161287184475, 178967047448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 63963136 65011712 153845760 159907840 ⟨⟨168401291631, 168401291645⟩, ⟨159773883472, 177257470954⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 65011712 66060288 147783680 153845760 ⟨⟨161714183697, 161714183703⟩, ⟨153185471432, 170472068050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 66060288 67108864 147783680 153845760 ⟨⟨160186884737, 160186884751⟩, ⟨151751108867, 168847767529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 65011712 66060288 153845760 159907840 ⟨⟨166819118285, 166819118287⟩, ⟨158285706087, 175577284527⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 66060288 67108864 153845760 159907840 ⟨⟨165263378341, 165263378354⟩, ⟨156821952160, 173925649339⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 62914560 67108864 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 65011712) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 63963136) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 63963136) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 66060288) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 66060288) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 65011712) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 63963136) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 63963136) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 153845760) (by decide) (join_su (m := 66060288) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 66060288) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/40 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
