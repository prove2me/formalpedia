-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_52428800_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:58:24.240362+00:00
-- url     : https://prove2.me/submissions/fc2fc983-9dfa-4b53-ad6c-1ed2262c0a9d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 1/16]`, `ρ ∈ [229/2560, 133/1280]` by 10 cells of the computing
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
theorem cell0 : cellOK 50331648 50855936 75038720 78069760 ⟨⟨109632350579, 109632350591⟩, ⟨104512341446, 114856782395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 50855936 51380224 75038720 78069760 ⟨⟨108905724230, 108905724246⟩, ⟨103825159399, 114089274780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 51380224 78069760 81100800 ⟨⟨112836474502, 112836474513⟩, ⟨105444231021, 120448309610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 51380224 51904512 75038720 78069760 ⟨⟨108188546236, 108188546248⟩, ⟨103146795720, 113331876122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 51904512 52428800 75038720 78069760 ⟨⟨107480619042, 107480619057⟩, ⟨102477067976, 112584372884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 51380224 52428800 78069760 81100800 ⟨⟨111369458288, 111369458301⟩, ⟨104085593564, 118867166636⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 50331648 51380224 81100800 84131840 ⟨⟨116361666876, 116361666892⟩, ⟨108961211349, 123978991821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 50331648 51380224 84131840 87162880 ⟨⟨119844572872, 119844572884⟩, ⟨112436712137, 127466619210⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 51380224 52428800 81100800 84131840 ⟨⟨114863201371, 114863201387⟩, ⟨107570584453, 122367075154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 51380224 52428800 84131840 87162880 ⟨⟨118315771153, 118315771169⟩, ⟨111015188868, 125825058758⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 52428800 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 51380224) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 50855936) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 78069760) (by decide) (join_su (m := 51904512) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 51380224) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 84131840) (by decide) (leaf_ok cell8) (leaf_ok cell9))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (1/16 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((52428800 : ℤ) : ℝ) / (D : ℝ)) = (1/16 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
