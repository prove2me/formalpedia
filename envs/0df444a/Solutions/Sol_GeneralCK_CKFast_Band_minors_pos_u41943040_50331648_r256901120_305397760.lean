-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r256901120_305397760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:51:46.109062+00:00
-- url     : https://prove2.me/submissions/c00e4b3e-21fd-4db1-b3e4-b98fc198da63

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 3/50]`, `ρ ∈ [49/160, 233/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 41943040 44040192 256901120 269025280 ⟨⟨294024668058, 294024668075⟩, ⟨273289692613, 315609189479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 44040192 46137344 256901120 269025280 ⟨⟨288899545463, 288899545476⟩, ⟨268604215558, 310021795001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 41943040 44040192 269025280 281149440 ⟨⟨302548535647, 302548535664⟩, ⟨281954291305, 323949405079⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 44040192 46137344 269025280 281149440 ⟨⟨297401386936, 297401386953⟩, ⟨277231876688, 318357322074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 46137344 48234496 256901120 269025280 ⟨⟨283937791721, 283937791734⟩, ⟨264064206154, 304616486337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 48234496 50331648 256901120 269025280 ⟨⟨279130225680, 279130225693⟩, ⟨259661623873, 299382913748⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 46137344 48234496 269025280 281149440 ⟨⟨292413637945, 292413637962⟩, ⟨272652050651, 312942110128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 48234496 50331648 269025280 281149440 ⟨⟨287576493449, 287576493462⟩, ⟨268207069050, 307693906551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 41943040 44040192 281149440 293273600 ⟨⟨310874727976, 310874727993⟩, ⟨290419710868, 332095947467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 44040192 46137344 281149440 293273600 ⟨⟨305709334400, 305709334413⟩, ⟨285664783385, 326502091943⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 41943040 44040192 293273600 305397760 ⟨⟨319016529431, 319016529448⟩, ⟨298698959183, 340062178303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 44040192 46137344 293273600 305397760 ⟨⟨313836194959, 313836194975⟩, ⟨293915437834, 334469041041⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 46137344 48234496 281149440 293273600 ⟨⟨300699453225, 300699453241⟩, ⟨281049567251, 321080074829⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 48234496 50331648 281149440 293273600 ⟨⟨295836651432, 295836651449⟩, ⟨276566600011, 315820485723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 46137344 48234496 293273600 305397760 ⟨⟨308807576026, 308807576042⟩, ⟨289268767727, 329042890819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 48234496 50331648 293273600 305397760 ⟨⟨303922579472, 303922579488⟩, ⟨284751753761, 323774737527⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 50331648 256901120 305397760 t = true :=
  ⟨_, (join_sr (m := 281149440) (by decide) (join_su (m := 46137344) (by decide) (join_sr (m := 269025280) (by decide) (join_su (m := 44040192) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 44040192) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 269025280) (by decide) (join_su (m := 48234496) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 48234496) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 46137344) (by decide) (join_sr (m := 293273600) (by decide) (join_su (m := 44040192) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 44040192) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 293273600) (by decide) (join_su (m := 48234496) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 48234496) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (49/160 : ℝ) (233/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  have e3 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
