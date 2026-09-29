-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r248381440_259522560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:32:42.595981+00:00
-- url     : https://prove2.me/submissions/e95db03e-abc3-45d5-8ad8-cb5a3123a4fc

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [379/1280, 99/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 248381440 251166720 ⟨⟨97406730034, 97406730041⟩, ⟨93971199703, 100884501812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 204472320 205783040 251166720 253952000 ⟨⟨98428235659, 98428235665⟩, ⟨94985089957, 101913639598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 205783040 207093760 248381440 251166720 ⟨⟨96609612019, 96609612024⟩, ⟨93190322392, 100070853121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 251166720 253952000 ⟨⟨97623721790, 97623721795⟩, ⟨94196843204, 101092569868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 205783040 253952000 256737280 ⟨⟨99448549950, 99448549956⟩, ⟨95997799054, 102941575563⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 204472320 205783040 256737280 259522560 ⟨⟨100467679640, 100467679648⟩, ⟨97009333667, 103968316506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205783040 207093760 253952000 256737280 ⟨⟨98636666155, 98636666160⟩, ⟨95202208416, 102113111100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 205783040 207093760 256737280 259522560 ⟨⟨99648451659, 99648451664⟩, ⟨96206424511, 103132483422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 208404480 248381440 251166720 ⟨⟨95817219614, 95817219622⟩, ⟨92414008067, 99262096357⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207093760 208404480 251166720 253952000 ⟨⟨96823956039, 96823956047⟩, ⟨93413182187, 100276414298⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 208404480 209715200 248381440 251166720 ⟨⟨95029484241, 95029484247⟩, ⟨91642190605, 98458160418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 208404480 209715200 251166720 253952000 ⟨⟨96028869666, 96028869672⟩, ⟨92634040613, 99465101634⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 207093760 208404480 253952000 256737280 ⟨⟨97829552519, 97829552526⟩, ⟨94411225804, 101289582554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 207093760 208404480 256737280 259522560 ⟨⟨98834015416, 98834015423⟩, ⟨95408145219, 102301607547⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209715200 253952000 256737280 ⟨⟨97027140149, 97027140155⟩, ⟨93624784762, 100470918533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 208404480 209715200 256737280 259522560 ⟨⟨98024301873, 98024301881⟩, ⟨94614429178, 101475617352⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 248381440 259522560 t = true :=
  ⟨_, (join_su (m := 207093760) (by decide) (join_sr (m := 253952000) (by decide) (join_su (m := 205783040) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 251166720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 205783040) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 256737280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 253952000) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 251166720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 251166720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 208404480) (by decide) (join_sr (m := 256737280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 256737280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (379/1280 : ℝ) (99/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  have e3 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
