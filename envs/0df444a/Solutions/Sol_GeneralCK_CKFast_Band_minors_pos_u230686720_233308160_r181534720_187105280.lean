-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_233308160_r181534720_187105280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:27:03.236848+00:00
-- url     : https://prove2.me/submissions/b8c4920c-a5c4-4257-acf1-42f5a877dd47

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 89/320]`, `ρ ∈ [277/1280, 571/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 230686720 231342080 181534720 182927360 ⟨⟨60899916781, 60899916785⟩, ⟨59410458861, 62398426327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 231342080 182927360 184320000 ⟨⟨61349529539, 61349529543⟩, ⟨59858277338, 62849838452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 231342080 231997440 181534720 182927360 ⟨⟨60629444745, 60629444751⟩, ⟨59143169894, 62124740752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 231342080 231997440 182927360 184320000 ⟨⟨61077190939, 61077190944⟩, ⟨59589126285, 62574281871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 231342080 184320000 185712640 ⟨⟨61798928007, 61798928011⟩, ⟨60305882116, 63301035681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 231342080 185712640 187105280 ⟨⟨62248112711, 62248112715⟩, ⟨60753273724, 63752018543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 231342080 231997440 184320000 185712640 ⟨⟨61524725477, 61524725482⟩, ⟨60034871595, 63023610746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 231342080 231997440 185712640 187105280 ⟨⟨61972048877, 61972048884⟩, ⟨60480406341, 63472727898⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 231997440 232652800 181534720 182927360 ⟨⟨60359723919, 60359723925⟩, ⟨58876616653, 61851822068⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 231997440 232652800 182927360 184320000 ⟨⟨60805607137, 60805607143⟩, ⟨59320714542, 62299495772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 232652800 233308160 181534720 182927360 ⟨⟨60090748756, 60090748763⟩, ⟨58610793704, 61579664614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 232652800 233308160 182927360 184320000 ⟨⟨60534772565, 60534772572⟩, ⟨59053036655, 62025474473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 231997440 232652800 184320000 185712640 ⟨⟨61251281306, 61251281311⟩, ⟨59764603941, 62746959858⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 231997440 232652800 185712640 187105280 ⟨⟨61696746938, 61696746945⟩, ⟨60208285359, 63194214839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 232652800 233308160 184320000 185712640 ⟨⟨60978589908, 60978589915⟩, ⟨59495073680, 62471077315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 232652800 233308160 185712640 187105280 ⟨⟨61422201287, 61422201294⟩, ⟨59936905281, 62916473642⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 233308160 181534720 187105280 t = true :=
  ⟨_, (join_su (m := 231997440) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 231342080) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 182927360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 231342080) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 185712640) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 184320000) (by decide) (join_su (m := 232652800) (by decide) (join_sr (m := 182927360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 182927360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 232652800) (by decide) (join_sr (m := 185712640) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 185712640) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (89/320 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (571/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((187105280 : ℤ) : ℝ) / (D : ℝ)) = (571/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
