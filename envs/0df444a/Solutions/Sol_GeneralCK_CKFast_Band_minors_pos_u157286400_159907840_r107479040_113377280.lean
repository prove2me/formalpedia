-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_159907840_r107479040_113377280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:24:28.236952+00:00
-- url     : https://prove2.me/submissions/5d22ba9f-c5f2-4920-8ffb-9f93592cb00e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 61/320]`, `ρ ∈ [41/320, 173/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 157941760 107479040 108953600 ⟨⟨60027519601, 60027519609⟩, ⟨58147853533, 61922198628⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157286400 157941760 108953600 110428160 ⟨⟨60802247593, 60802247599⟩, ⟨58919853178, 62699650271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157941760 158597120 107479040 108953600 ⟨⟨59763018975, 59763018981⟩, ⟨57889250459, 61651716028⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 157941760 158597120 108953600 110428160 ⟨⟨60534661769, 60534661775⟩, ⟨58658172827, 62426074771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 157286400 157941760 110428160 111902720 ⟨⟨61575934363, 61575934369⟩, ⟨59690818572, 63476053669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157286400 157941760 111902720 113377280 ⟨⟨62348584227, 62348584235⟩, ⟨60460753997, 64251413178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 157941760 158597120 110428160 111902720 ⟨⟨61305275257, 61305275264⟩, ⟨59426072754, 63199397293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 157941760 158597120 111902720 113377280 ⟨⟨62074863688, 62074863696⟩, ⟨60192954451, 63971687881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 158597120 159252480 107479040 108953600 ⟨⟨59499903278, 59499903281⟩, ⟨57631989642, 61382661855⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 158597120 159252480 108953600 110428160 ⟨⟨60268473328, 60268473331⟩, ⟨58397847177, 62153940154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 159252480 159907840 107479040 108953600 ⟨⟨59238158647, 59238158654⟩, ⟨57376057691, 61115021765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 159252480 159907840 108953600 110428160 ⟨⟨60003668308, 60003668316⟩, ⟨58138862744, 61883231984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 158597120 159252480 110428160 111902720 ⟨⟨61036025854, 61036025857⟩, ⟨59162693948, 62924194121⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 158597120 159252480 111902720 113377280 ⟨⟨61802565035, 61802565036⟩, ⟨59926534096, 63693427969⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 159252480 159907840 110428160 111902720 ⟨⟨60768172093, 60768172101⟩, ⟨58900668573, 62650429620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 159252480 159907840 111902720 113377280 ⟨⟨61531674110, 61531674118⟩, ⟨59661479255, 63416618820⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 159907840 107479040 113377280 t = true :=
  ⟨_, (join_su (m := 158597120) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 157941760) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 108953600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 157941760) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 111902720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 110428160) (by decide) (join_su (m := 159252480) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 108953600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 159252480) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 111902720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (61/320 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (173/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
