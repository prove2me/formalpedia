-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u180879360_183500800_r170393600_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:55.700705+00:00
-- url     : https://prove2.me/submissions/8d81edd0-d586-4880-a8a8-b67cee389567

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [69/320, 7/32]`, `ρ ∈ [13/64, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 180879360 181534720 170393600 173178880 ⟨⟨79615584335, 79615584341⟩, ⟨77466322463, 81783031135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 181534720 182190080 170393600 173178880 ⟨⟨79284048985, 79284048990⟩, ⟨77141379263, 81444813499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 180879360 181534720 173178880 175964160 ⟨⟨80830247340, 80830247346⟩, ⟨78676224521, 83002445421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 181534720 182190080 173178880 175964160 ⟨⟨80494218506, 80494218511⟩, ⟨78346798664, 82659723889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 182190080 182845440 170393600 173178880 ⟨⟨78953831274, 78953831282⟩, ⟨76817715413, 81107952513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 182845440 183500800 170393600 173178880 ⟨⟨78624920124, 78624920130⟩, ⟨76495320177, 80772436733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 182190080 182845440 173178880 175964160 ⟨⟨80159518986, 80159518992⟩, ⟨78018663863, 82318370639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 182845440 183500800 173178880 175964160 ⟨⟨79826137632, 79826137640⟩, ⟨77691809319, 81978374164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 180879360 181534720 175964160 178749440 ⟨⟨82042806963, 82042806969⟩, ⟨79884038360, 84219741027⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 181534720 182190080 175964160 178749440 ⟨⟨81702307656, 81702307658⟩, ⟨79550152625, 83872538837⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 180879360 181534720 178749440 181534720 ⟨⟨83253276820, 83253276827⟩, ⟨81089777473, 85434931697⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 181534720 182190080 178749440 181534720 ⟨⟨82908329844, 82908329849⟩, ⟨80751454443, 85083271880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 182190080 182845440 175964160 178749440 ⟨⟨81363149105, 81363149111⟩, ⟨79217569431, 83526716330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 182845440 183500800 175964160 178749440 ⟨⟨81025320106, 81025320112⟩, ⟨78886277910, 83182261940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 182190080 182845440 178749440 181534720 ⟨⟨82564734846, 82564734853⟩, ⟨80414445210, 84733002921⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 182845440 183500800 178749440 181534720 ⟨⟨82222480558, 82222480566⟩, ⟨80078738854, 84384113193⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 180879360 183500800 170393600 181534720 t = true :=
  ⟨_, (join_sr (m := 175964160) (by decide) (join_su (m := 182190080) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 181534720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 181534720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 173178880) (by decide) (join_su (m := 182845440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 182845440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 182190080) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 181534720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 181534720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 178749440) (by decide) (join_su (m := 182845440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 182845440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (69/320 : ℝ) (7/32 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((180879360 : ℤ) : ℝ) / (D : ℝ)) = (69/320 : ℝ) := by norm_num [D]
  have e1 : (((183500800 : ℤ) : ℝ) / (D : ℝ)) = (7/32 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
