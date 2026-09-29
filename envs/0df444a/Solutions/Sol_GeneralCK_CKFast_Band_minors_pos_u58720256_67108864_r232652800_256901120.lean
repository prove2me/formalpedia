-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_67108864_r232652800_256901120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:15:49.522625+00:00
-- url     : https://prove2.me/submissions/3a13a495-f6fc-49c4-899e-c2cc81a30d62

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 2/25]`, `ρ ∈ [71/256, 49/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 58720256 60817408 232652800 238714880 ⟨⟨237892615066, 237892615081⟩, ⟨224608887905, 251603648835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 58720256 60817408 238714880 244776960 ⟨⟨242252201764, 242252201777⟩, ⟨228976191861, 255947518204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 60817408 62914560 232652800 238714880 ⟨⟨233971756776, 233971756788⟩, ⟨220935277409, 247424394598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 60817408 62914560 238714880 244776960 ⟨⟨238303001875, 238303001891⟩, ⟨225271131152, 251743501220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 58720256 60817408 244776960 250839040 ⟨⟨246562408669, 246562408681⟩, ⟨233294740585, 260241553685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 58720256 60817408 250839040 256901120 ⟨⟨250824796406, 250824796418⟩, ⟨237566044104, 264487361567⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 60817408 62914560 244776960 250839040 ⟨⟨242586180130, 242586180142⟩, ⟨229559573085, 256014039459⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 60817408 62914560 250839040 256901120 ⟨⟨246822783539, 246822783551⟩, ⟨233802045834, 260237546471⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 62914560 65011712 232652800 238714880 ⟨⟨230161597169, 230161597181⟩, ⟨217363137098, 243365513172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 62914560 65011712 238714880 244776960 ⟨⟨234463706310, 234463706324⟩, ⟨221666981693, 247658796485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 65011712 67108864 232652800 238714880 ⟨⟨226456750534, 226456750545⟩, ⟨213887599155, 239421078719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 65011712 67108864 238714880 244776960 ⟨⟨230729023689, 230729023700⟩, ⟨218158951316, 243687593535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 62914560 65011712 244776960 250839040 ⟨⟨238719039825, 238719039840⟩, ⟨225924729874, 251904763143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 62914560 65011712 250839040 256901120 ⟨⟨242929023965, 242929023976⟩, ⟨230137759851, 256104883822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 65011712 67108864 244776960 250839040 ⟨⟨234955789319, 234955789330⟩, ⟨222385493815, 247908027308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 65011712 67108864 250839040 256901120 ⟨⟨239138410706, 239138410721⟩, ⟨226568543339, 252083786842⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 67108864 232652800 256901120 t = true :=
  ⟨_, (join_su (m := 62914560) (by decide) (join_sr (m := 244776960) (by decide) (join_su (m := 60817408) (by decide) (join_sr (m := 238714880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 238714880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 60817408) (by decide) (join_sr (m := 250839040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 250839040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 244776960) (by decide) (join_su (m := 65011712) (by decide) (join_sr (m := 238714880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 238714880) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 65011712) (by decide) (join_sr (m := 250839040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 250839040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (71/256 : ℝ) (49/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  have e3 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
