-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r208404480_232652800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:50:46.079224+00:00
-- url     : https://prove2.me/submissions/a03c5dfd-d5cc-4e6e-8422-6fed3acede67

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 3/50]`, `ρ ∈ [159/640, 71/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 41943040 44040192 208404480 214466560 ⟨⟨255223955478, 255223955492⟩, ⟨239375834542, 271664933485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 41943040 44040192 214466560 220528640 ⟨⟨260032260030, 260032260044⟩, ⟨244227528752, 276414848685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 44040192 46137344 208404480 214466560 ⟨⟨250249220262, 250249220278⟩, ⟨234772452577, 266299406400⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 44040192 46137344 214466560 220528640 ⟨⟨255033906150, 255033906167⟩, ⟨239594053036, 271033197193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 41943040 44040192 220528640 226590720 ⟨⟨264770106473, 264770106487⟩, ⟨249009037641, 281094500657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 41943040 44040192 226590720 232652800 ⟨⟨269440227288, 269440227305⟩, ⟨253723018740, 285706677106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 44040192 46137344 220528640 226590720 ⟨⟨259749960862, 259749960879⟩, ⟨244347427542, 275698369289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 44040192 46137344 226590720 232652800 ⟨⟨264399990848, 264399990866⟩, ⟨249035106471, 280297588358⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 46137344 48234496 208404480 214466560 ⟨⟨245455256515, 245455256531⟩, ⟨230332244509, 261133201893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 46137344 48234496 214466560 220528640 ⟨⟨250214268314, 250214268328⟩, ⟨235122255510, 265848172487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 48234496 50331648 208404480 214466560 ⟨⟨240830948976, 240830948992⟩, ⟨226045357175, 256153886476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 48234496 50331648 214466560 220528640 ⟨⟨245562484970, 245562484983⟩, ⟨230802482974, 260847656083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 46137344 48234496 220528640 226590720 ⟨⟨254906469127, 254906469143⟩, ⟨239845971645, 270496189266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 46137344 48234496 226590720 232652800 ⟨⟨259534344250, 259534344264⟩, ⟨244505801871, 275079799475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 48234496 50331648 220528640 226590720 ⟨⟨250229016269, 250229016282⟩, ⟨235495212487, 265476146348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 48234496 50331648 226590720 232652800 ⟨⟨254832911937, 254832911950⟩, ⟨240125838877, 270041789971⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 50331648 208404480 232652800 t = true :=
  ⟨_, (join_su (m := 46137344) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 44040192) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 214466560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 44040192) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 226590720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 220528640) (by decide) (join_su (m := 48234496) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 214466560) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 48234496) (by decide) (join_sr (m := 226590720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 226590720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (159/640 : ℝ) (71/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  have e3 : (((232652800 : ℤ) : ℝ) / (D : ℝ)) = (71/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
