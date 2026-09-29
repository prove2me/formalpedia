-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:22:43.596713+00:00
-- url     : https://prove2.me/submissions/0e9bc0ce-97bd-4bce-8c4c-ddc8dd8fb549

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 7/200]`, `ρ ∈ [133/1280, 303/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 25165824 26214400 87162880 90193920 ⟨⟨178228549593, 178228549612⟩, ⟨166630903446, 190283265896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 25165824 26214400 90193920 93224960 ⟨⟨182348796258, 182348796282⟩, ⟨170790558053, 194353348614⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 26214400 27262976 87162880 90193920 ⟨⟨174934630285, 174934630303⟩, ⟨163610516732, 186697903643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 26214400 27262976 90193920 93224960 ⟨⟨179027144222, 179027144241⟩, ⟨167738174782, 190745253130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 25165824 26214400 93224960 96256000 ⟨⟨186394248259, 186394248283⟩, ⟨174875983769, 198348416608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 25165824 26214400 96256000 99287040 ⟨⟨190367819651, 190367819674⟩, ⟨178890002799, 202271461979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 26214400 27262976 93224960 96256000 ⟨⟨183046916034, 183046916057⟩, ⟨171793721821, 194719540368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 26214400 27262976 96256000 99287040 ⟨⟨186996721607, 186996721631⟩, ⟨175779844000, 198623619079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 27262976 28311552 87162880 90193920 ⟨⟨171767382450, 171767382468⟩, ⟨160703567541, 183253523340⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 27262976 28311552 90193920 93224960 ⟨⟨175831374106, 175831374128⟩, ⟨164798811719, 187276914834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 28311552 29360128 87162880 90193920 ⟨⟨168719089946, 168719089963⟩, ⟨157903282206, 179941381172⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 28311552 29360128 90193920 93224960 ⟨⟨172753912884, 172753912902⟩, ⟨161965801202, 183939776630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 27262976 28311552 93224960 96256000 ⟨⟨179824624472, 179824624495⟩, ⟨168823998807, 191229161040⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 27262976 28311552 96256000 99287040 ⟨⟨183749778485, 183749778502⟩, ⟨172781686423, 195112983938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 28311552 29360128 93224960 96256000 ⟨⟨176719942405, 176719942427⟩, ⟨165960253604, 187868904705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 28311552 29360128 96256000 99287040 ⟨⟨180619699374, 180619699396⟩, ⟨169889075577, 191731362081⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 29360128 87162880 99287040 t = true :=
  ⟨_, (join_su (m := 27262976) (by decide) (join_sr (m := 93224960) (by decide) (join_su (m := 26214400) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 90193920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 26214400) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 96256000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 93224960) (by decide) (join_su (m := 28311552) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 90193920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 28311552) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 96256000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (7/200 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((29360128 : ℤ) : ℝ) / (D : ℝ)) = (7/200 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
