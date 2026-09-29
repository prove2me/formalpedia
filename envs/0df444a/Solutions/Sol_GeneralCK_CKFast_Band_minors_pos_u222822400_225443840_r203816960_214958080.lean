-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_225443840_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:59:30.766783+00:00
-- url     : https://prove2.me/submissions/b1441769-e711-4988-82cd-30473e2b3a78

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 43/160]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 222822400 223477760 203816960 206602240 ⟨⟨71967860470, 71967860476⟩, ⟨70127486773, 73821905647⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 223477760 224133120 203816960 206602240 ⟨⟨71656762512, 71656762518⟩, ⟨69821222745, 73505919145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 223477760 206602240 209387520 ⟨⟨72904195281, 72904195286⟩, ⟨71059839451, 74762228872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223477760 224133120 206602240 209387520 ⟨⟨72589373285, 72589373291⟩, ⟨70749861443, 74442508438⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 224133120 224788480 203816960 206602240 ⟨⟨71346545755, 71346545757⟩, ⟨69515817566, 73190836542⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 224788480 225443840 203816960 206602240 ⟨⟨71037203732, 71037203738⟩, ⟨69211264941, 72876651206⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 224133120 224788480 206602240 209387520 ⟨⟨72275439203, 72275439206⟩, ⟨70440749000, 74123698609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224788480 225443840 206602240 209387520 ⟨⟨71962386533, 71962386540⟩, ⟨70132495794, 73805792718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 223477760 209387520 212172800 ⟨⟨73839581480, 73839581488⟩, ⟨71991248055, 75701598876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 223477760 224133120 209387520 212172800 ⟨⟨73521046678, 73521046684⟩, ⟨71677567198, 75378155839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222822400 223477760 212172800 214958080 ⟨⟨74774023948, 74774023954⟩, ⟨72921717434, 76640020566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 223477760 224133120 212172800 214958080 ⟨⟨74451787493, 74451787500⟩, ⟨72604344788, 76312866178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224133120 224788480 209387520 212172800 ⟨⟨73203406391, 73203406394⟩, ⟨71364758516, 75055630001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224788480 225443840 209387520 212172800 ⟨⟨72886654087, 72886654093⟩, ⟨71052815645, 74734014663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224133120 224788480 212172800 214958080 ⟨⟨74130452051, 74130452053⟩, ⟨72287850819, 75986635475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224788480 225443840 212172800 214958080 ⟨⟨73810011052, 73810011059⟩, ⟨71972229131, 75661321726⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 225443840 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 223477760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 223477760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 224788480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 224788480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 224133120) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 223477760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 223477760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 224788480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 224788480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
