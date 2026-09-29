-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_161218560_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:17:14.841257+00:00
-- url     : https://prove2.me/submissions/bd2b884b-b7f4-4fa1-bb6f-65bbeff392d3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 123/640]`, `ρ ∈ [137/1280, 73/640]` by 12 cells of the computing
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
theorem cell0 : cellOK 159907840 160235520 89784320 91258880 ⟨⟨49804782135, 49804782141⟩, ⟨48664545151, 50950837597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 160235520 160563200 89784320 91258880 ⟨⟨49693636494, 49693636500⟩, ⟨48555379041, 50837694180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 159907840 160235520 91258880 92733440 ⟨⟨50580295679, 50580295685⟩, ⟨49438473706, 51727932926⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160235520 160563200 91258880 92733440 ⟨⟨50467557679, 50467557687⟩, ⟨49327718047, 51613194389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 160563200 160890880 89784320 91258880 ⟨⟨49582786911, 49582786917⟩, ⟨48446502064, 50724853833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 160890880 161218560 89784320 91258880 ⟨⟨49472231878, 49472231884⟩, ⟨48337912752, 50612315014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 160563200 160890880 91258880 92733440 ⟨⟨50355119188, 50355119195⟩, ⟨49217254967, 51498762377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 160890880 161218560 91258880 92733440 ⟨⟨50242978682, 50242978690⟩, ⟨49107082985, 51384635331⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 159907840 160563200 92733440 94208000 ⟨⟨51297561547, 51297561553⟩, ⟨49468566751, 53141272267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 159907840 160563200 94208000 95682560 ⟨⟨52070193716, 52070193722⟩, ⟨50238434752, 53916665260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 160563200 161218560 92733440 94208000 ⟨⟨51069518566, 51069518574⟩, ⟨49246168825, 52907501041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 160563200 161218560 94208000 95682560 ⟨⟨51838997252, 51838997260⟩, ⟨50012892282, 53679731810⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 161218560 89784320 95682560 t = true :=
  ⟨_, (join_sr (m := 92733440) (by decide) (join_su (m := 160563200) (by decide) (join_sr (m := 91258880) (by decide) (join_su (m := 160235520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 160235520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 91258880) (by decide) (join_su (m := 160890880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 160890880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 160563200) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 94208000) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (123/640 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((161218560 : ℤ) : ℝ) / (D : ℝ)) = (123/640 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
