-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_235929600_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:41:55.635425+00:00
-- url     : https://prove2.me/submissions/9ecb9540-77c1-42f1-a802-07efff304781

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 9/32]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 233308160 233963520 248381440 251166720 ⟨⟨81041426956, 81041426962⟩, ⟨79215033749, 82880788105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233963520 234618880 248381440 251166720 ⟨⟨80686869227, 80686869230⟩, ⟨78865123470, 82521535649⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233963520 251166720 253952000 ⟨⟨81906908865, 81906908871⟩, ⟨80076742443, 83750050834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233963520 234618880 251166720 253952000 ⟨⟨81548877058, 81548877061⟩, ⟨79723366940, 83387315587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 234618880 235274240 248381440 251166720 ⟨⟨80333183257, 80333183262⟩, ⟨78516065185, 82163174995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235274240 235929600 248381440 251166720 ⟨⟨79980362951, 79980362956⟩, ⟨78167852930, 81805699905⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 234618880 235274240 251166720 253952000 ⟨⟨81191721758, 81191721765⟩, ⟨79370848191, 83025476874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235274240 235929600 251166720 253952000 ⟨⟨80835436849, 80835436855⟩, ⟨79019180211, 82664528436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233963520 253952000 256737280 ⟨⟨82771668529, 82771668535⟩, ⟨80937731734, 84618588416⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233963520 234618880 253952000 256737280 ⟨⟨82410171344, 82410171347⟩, ⟨80580899631, 84252379148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233963520 256737280 259522560 ⟨⟨83635709527, 83635709535⟩, ⟨81798005183, 85486404446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233963520 234618880 256737280 259522560 ⟨⟨83270755607, 83270755610⟩, ⟨81437725051, 85116729876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 234618880 235274240 253952000 256737280 ⟨⟨82049555328, 82049555334⟩, ⟨80224928960, 83887071065⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235274240 235929600 253952000 256737280 ⟨⟨81689814348, 81689814354⟩, ⟨79869813717, 83522657883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235274240 256737280 259522560 ⟨⟨82906687439, 82906687445⟩, ⟨81078310950, 84747961055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235274240 235929600 256737280 259522560 ⟨⟨82543498869, 82543498874⟩, ⟨80719756852, 84380091684⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 235929600 248381440 259522560 t = true :=
  ⟨_, (join_sr (m := 253952000) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 251166720) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233963520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 251166720) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235274240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 234618880) (by decide) (join_sr (m := 256737280) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 233963520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 256737280) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235274240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
