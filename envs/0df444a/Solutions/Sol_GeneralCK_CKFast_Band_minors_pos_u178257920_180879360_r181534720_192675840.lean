-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u178257920_180879360_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:55.851773+00:00
-- url     : https://prove2.me/submissions/597b4664-04f2-4a6c-bc22-e52498a7a059

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/80, 69/320]`, `ρ ∈ [277/1280, 147/640]` by 13 cells of the computing
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
theorem cell0 : cellOK 178257920 178913280 181534720 184320000 ⟨⟨85873019188, 85873019191⟩, ⟨83677879178, 88086665598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 178913280 179568640 181534720 184320000 ⟨⟨85518079517, 85518079523⟩, ⟨83329729701, 87724844430⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 178257920 178913280 184320000 187105280 ⟨⟨87097069483, 87097069486⟩, ⟨84897189205, 89315444234⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 178913280 179568640 184320000 187105280 ⟨⟨86737683488, 86737683494⟩, ⟨84544603138, 88949167449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 179568640 180224000 181534720 184320000 ⟨⟨85164549360, 85164549367⟩, ⟨82982950174, 87364473058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 180224000 180879360 181534720 184320000 ⟨⟨84812416896, 84812416903⟩, ⟨82637529137, 87005539289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 179568640 180224000 184320000 187105280 ⟨⟨86379718007, 86379718015⟩, ⟨84193398074, 88584351403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 180224000 180879360 184320000 187105280 ⟨⟨86023161166, 86023161172⟩, ⟨83843562493, 88220983852⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 178257920 179568640 187105280 189890560 ⟨⟨88136894947, 88136894953⟩, ⟨84520924113, 91802043275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 178257920 179568640 189890560 192675840 ⟨⟨89354476672, 89354476678⟩, ⟨85729967135, 93028156855⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 179568640 180224000 187105280 189890560 ⟨⟨87592792069, 87592792077⟩, ⟨85401766507, 89802119912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 180224000 180879360 187105280 189890560 ⟨⟨87231833501, 87231833509⟩, ⟨85047538813, 89434341450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 179568640 180879360 189890560 192675840 ⟨⟨88620938266, 88620938267⟩, ⟨85015998731, 92274625679⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 178257920 180879360 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 179568640) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 178913280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 178913280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 180224000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 180224000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 179568640) (by decide) (join_sr (m := 189890560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 189890560) (by decide) (join_su (m := 180224000) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/80 : ℝ) (69/320 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e1 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
