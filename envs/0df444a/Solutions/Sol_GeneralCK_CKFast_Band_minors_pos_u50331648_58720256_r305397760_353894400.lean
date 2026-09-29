-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_58720256_r305397760_353894400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:18:47.45853+00:00
-- url     : https://prove2.me/submissions/946fa049-1e4e-44ea-8f99-722f850de152

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 7/100]`, `ρ ∈ [233/640, 27/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 52428800 305397760 317521920 ⟨⟨307074126899, 307074126915⟩, ⟨288346280673, 326439257444⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 52428800 54525952 305397760 317521920 ⟨⟨302429539043, 302429539060⟩, ⟨284034168720, 321449283504⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 52428800 317521920 329646080 ⟨⟨314823965828, 314823965842⟩, ⟨296183987756, 334073340420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 52428800 54525952 317521920 329646080 ⟨⟨310157142474, 310157142487⟩, ⟨291840029566, 329072084317⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 54525952 56623104 305397760 317521920 ⟨⟨297905286034, 297905286049⟩, ⟨279831317940, 316591034784⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 56623104 58720256 305397760 317521920 ⟨⟨293495677463, 293495677479⟩, ⟨275732623876, 311858232369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 54525952 56623104 317521920 329646080 ⟨⟨305608099101, 305608099116⟩, ⟨287603378646, 324199327663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 56623104 58720256 317521920 329646080 ⟨⟨301171352210, 301171352225⟩, ⟨283469096271, 319449043726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 50331648 52428800 329646080 341770240 ⟨⟨322432204133, 322432204149⟩, ⟨303879607365, 341567608144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 52428800 54525952 329646080 341770240 ⟨⟨317745664796, 317745664812⟩, ⟨299506658206, 336557150748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 50331648 52428800 341770240 353894400 ⟨⟨329907103262, 329907103278⟩, ⟨311441225598, 348930410872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 52428800 54525952 341770240 353894400 ⟨⟨325203100685, 325203100700⟩, ⟨307041862396, 343912587043⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 54525952 56623104 329646080 341770240 ⟨⟨313174391624, 313174391640⟩, ⟨295239066057, 331672053512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 56623104 58720256 329646080 341770240 ⟨⟨308713097083, 308713097098⟩, ⟨291072050606, 326906526688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 54525952 56623104 341770240 353894400 ⟨⟨320611895959, 320611895972⟩, ⟨302745916672, 339017071462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 56623104 58720256 341770240 353894400 ⟨⟨316128387117, 316128387129⟩, ⟨298548759396, 334238297134⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 58720256 305397760 353894400 t = true :=
  ⟨_, (join_sr (m := 329646080) (by decide) (join_su (m := 54525952) (by decide) (join_sr (m := 317521920) (by decide) (join_su (m := 52428800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 52428800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 317521920) (by decide) (join_su (m := 56623104) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 56623104) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 54525952) (by decide) (join_sr (m := 341770240) (by decide) (join_su (m := 52428800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 52428800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 341770240) (by decide) (join_su (m := 56623104) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 56623104) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (7/100 : ℝ) →
    rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e2 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  have e3 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
