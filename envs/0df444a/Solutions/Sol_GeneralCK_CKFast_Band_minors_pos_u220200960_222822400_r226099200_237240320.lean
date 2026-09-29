-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_222822400_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:19:06.507527+00:00
-- url     : https://prove2.me/submissions/dd8c6832-fe75-4f70-a203-201d3c04fd84

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 17/64]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 220856320 226099200 228884480 ⟨⟨80804024143, 80804024149⟩, ⟨78912045963, 82709938489⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220856320 221511680 226099200 228884480 ⟨⟨80459648416, 80459648419⟩, ⟨78572672731, 82360505626⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220200960 220856320 228884480 231669760 ⟨⟨81747509466, 81747509474⟩, ⟨79851547666, 83657412419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 220856320 221511680 228884480 231669760 ⟨⟨81399473774, 81399473777⟩, ⟨79508523705, 83304310534⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 221511680 222167040 226099200 228884480 ⟨⟨80116231991, 80116231998⟩, ⟨78234235852, 82012055366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222167040 222822400 226099200 228884480 ⟨⟨79773767940, 79773767947⟩, ⟨77896728559, 81664580597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222167040 228884480 231669760 ⟨⟨81052403362, 81052403368⟩, ⟨79166442090, 82952197208⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222167040 222822400 228884480 231669760 ⟨⟨80706291271, 80706291277⟩, ⟨78825296024, 82601065307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 220200960 220856320 231669760 234455040 ⟨⟨82690040906, 82690040911⟩, ⟨80790100193, 84603927678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 220856320 221511680 231669760 234455040 ⟨⟨82338356319, 82338356321⟩, ⟨80443436478, 84247167939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 220200960 220856320 234455040 237240320 ⟨⟨83631623445, 83631623452⟩, ⟨81727708501, 85549489282⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 220856320 221511680 234455040 237240320 ⟨⟨83276300963, 83276300966⟩, ⟨81377415934, 85189082785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 221511680 222167040 231669760 234455040 ⟨⟨81987642885, 81987642890⟩, ⟨80097720997, 83891402613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 222167040 222822400 231669760 234455040 ⟨⟨81637893617, 81637893623⟩, ⟨79752946927, 83536624537⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 221511680 222167040 234455040 237240320 ⟨⟨82921955402, 82921955408⟩, ⟨81028077387, 84829676447⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 222167040 222822400 234455040 237240320 ⟨⟨82568579749, 82568579756⟩, ⟨80679686011, 84471263083⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 222822400 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 220856320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 222167040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 221511680) (by decide) (join_sr (m := 234455040) (by decide) (join_su (m := 220856320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 220856320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 234455040) (by decide) (join_su (m := 222167040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 222167040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
