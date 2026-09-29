-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u207093760_209715200_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:27:02.006405+00:00
-- url     : https://prove2.me/submissions/71017734-5e66-453d-8cb0-549a1d43aab0

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [79/320, 1/4]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 207093760 207749120 214958080 217743360 ⟨⟨83820159155, 83820159162⟩, ⟨81839759041, 85815660046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 207749120 208404480 214958080 217743360 ⟨⟨83470323324, 83470323327⟩, ⟨81495386899, 85460297490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 207093760 207749120 217743360 220528640 ⟨⟨84843004205, 84843004213⟩, ⟨82858412000, 86842698371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 207749120 208404480 217743360 220528640 ⟨⟨84489328599, 84489328601⟩, ⟨82510209361, 86483486994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 208404480 209059840 214958080 217743360 ⟨⟨83121571212, 83121571218⟩, ⟨81152071637, 85106045914⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209059840 209715200 214958080 217743360 ⟨⟨82773894714, 82773894721⟩, ⟨80809805355, 84752897000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 208404480 209059840 217743360 220528640 ⟨⟨84136743753, 84136743761⟩, ⟨82163070670, 86125393616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 209059840 209715200 217743360 220528640 ⟨⟨83785241536, 83785241544⟩, ⟨81816987995, 85768409883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 207749120 220528640 223313920 ⟨⟨85864623417, 85864623424⟩, ⟨83875846185, 87868503698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207749120 208404480 220528640 223313920 ⟨⟨85507121791, 85507121794⟩, ⟨83523826683, 87505457382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 207749120 223313920 226099200 ⟨⟨86885023617, 86885023624⟩, ⟨84892068381, 88893082895⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207749120 208404480 223313920 226099200 ⟨⟨86523709629, 86523709633⟩, ⟨84536245549, 88526215424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 208404480 209059840 220528640 223313920 ⟨⟨85150717842, 85150717848⟩, ⟨83172878068, 87143535952⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 209059840 209715200 220528640 223313920 ⟨⟨84795403404, 84795403410⟩, ⟨82822992379, 86782731023⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209059840 223313920 226099200 ⟨⟨86163500105, 86163500112⟩, ⟨84181500417, 88160479594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 209059840 209715200 223313920 226099200 ⟨⟨85804386850, 85804386856⟩, ⟨83827824994, 87795866995⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 207093760 209715200 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 207749120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 209059840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 208404480) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 207749120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 207749120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 209059840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 209059840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (79/320 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((207093760 : ℤ) : ℝ) / (D : ℝ)) = (79/320 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
