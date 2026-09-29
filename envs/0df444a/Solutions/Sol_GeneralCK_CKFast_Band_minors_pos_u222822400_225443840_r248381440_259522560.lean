-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_225443840_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:34:46.099055+00:00
-- url     : https://prove2.me/submissions/d8a6e208-fe3d-491c-a6ba-beeb3002ac3e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 43/160]`, `ρ ∈ [379/1280, 99/320]` by 15 cells of the computing
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
theorem cell0 : cellOK 222822400 223477760 248381440 251166720 ⟨⟨86838074509, 86838074517⟩, ⟨84934516370, 88755395708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 223477760 224133120 248381440 251166720 ⟨⟨86468699391, 86468699398⟩, ⟨84570124757, 88380985159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 223477760 251166720 253952000 ⟨⟨87759804340, 87759804347⟩, ⟨85852333534, 89681043295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223477760 224133120 251166720 253952000 ⟨⟨87386876343, 87386876350⟩, ⟨85484397618, 89303071470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 224133120 224788480 248381440 251166720 ⟨⟨86100300325, 86100300328⟩, ⟨84206687048, 88007573117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 224788480 225443840 248381440 251166720 ⟨⟨85732870395, 85732870403⟩, ⟨83844196490, 87635152511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 224133120 224788480 251166720 253952000 ⟨⟨87014929480, 87014929483⟩, ⟨85117420706, 88926103208⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224788480 225443840 251166720 253952000 ⟨⟨86643956816, 86643956823⟩, ⟨84751396030, 88550131419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 223477760 253952000 256737280 ⟨⟨88680660956, 88680660962⟩, ⟨86769281612, 90605813467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 223477760 224133120 253952000 256737280 ⟨⟨88304190195, 88304190202⟩, ⟨86397811418, 90224290566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222822400 224133120 256737280 259522560 ⟨⟨89410522838, 89410522845⟩, ⟨86166748797, 92692886141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224133120 224788480 253952000 256737280 ⟨⟨87928705557, 87928705560⟩, ⟨86027305241, 89843776193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224788480 225443840 253952000 256737280 ⟨⟨87554200085, 87554200092⟩, ⟨85657756288, 89464263237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 224788480 256737280 259522560 ⟨⟨88841632958, 88841632961⟩, ⟨86936345031, 90760596500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224788480 225443840 256737280 259522560 ⟨⟨88463604544, 88463604550⟩, ⟨86563281581, 90377552327⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 225443840 248381440 259522560 t = true :=
  ⟨_, (join_sr (m := 253952000) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 251166720) (by decide) (join_su (m := 223477760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 223477760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 251166720) (by decide) (join_su (m := 224788480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 224788480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 224133120) (by decide) (join_sr (m := 256737280) (by decide) (join_su (m := 223477760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 256737280) (by decide) (join_su (m := 224788480) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 224788480) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
