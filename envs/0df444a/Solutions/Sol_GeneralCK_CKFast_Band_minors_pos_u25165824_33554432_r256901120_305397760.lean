-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r256901120_305397760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:29:42.453268+00:00
-- url     : https://prove2.me/submissions/f0683e8a-5a2c-46b7-bfc6-7050777c4efe

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 1/25]`, `ρ ∈ [49/160, 233/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 25165824 27262976 256901120 269025280 ⟨⟨342353510421, 342353510426⟩, ⟨317269852776, 368499111630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 27262976 29360128 256901120 269025280 ⟨⟨335458171243, 335458171259⟩, ⟨311017972065, 360930752970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 25165824 27262976 269025280 281149440 ⟨⟨350846385437, 350846385451⟩, ⟨326076852150, 376608119872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 27262976 29360128 269025280 281149440 ⟨⟨343981593883, 343981593902⟩, ⟨319827076312, 369102999740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 29360128 31457280 256901120 269025280 ⟨⟨328843481579, 328843481595⟩, ⟨305013137770, 353677440333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 31457280 33554432 256901120 269025280 ⟨⟨322488492248, 322488492263⟩, ⟨299237374014, 346715315750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 29360128 31457280 269025280 281149440 ⟨⟨337388110655, 337388110675⟩, ⟨313817337990, 361900952099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 31457280 33554432 269025280 281149440 ⟨⟨331045983442, 331045983460⟩, ⟨308030426656, 354979372238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 25165824 27262976 281149440 293273600 ⟨⟨359118802320, 359118802333⟩, ⟨334652254710, 384513148347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 27262976 29360128 281149440 293273600 ⟨⟨352286180249, 352286180268⟩, ⟨328408017163, 377070583828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 25165824 27262976 293273600 305397760 ⟨⟨367187822807, 367187822819⟩, ⟨343013513733, 392230315792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 27262976 29360128 293273600 305397760 ⟨⟨360388568772, 360388568792⟩, ⟨336777675512, 384849416338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 29360128 31457280 281149440 293273600 ⟨⟨345716014866, 345716014885⟩, ⟨322397077787, 369919876266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 31457280 33554432 281149440 293273600 ⟨⟨339389267161, 339389267179⟩, ⟨316602935347, 363039557918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 29360128 31457280 293273600 305397760 ⟨⟨353843381774, 353843381794⟩, ⟨330768663269, 377749855315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 31457280 33554432 293273600 305397760 ⟨⟨347534061123, 347534061141⟩, ⟨324970633725, 370911199177⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 33554432 256901120 305397760 t = true :=
  ⟨_, (join_sr (m := 281149440) (by decide) (join_su (m := 29360128) (by decide) (join_sr (m := 269025280) (by decide) (join_su (m := 27262976) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 27262976) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 269025280) (by decide) (join_su (m := 31457280) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 31457280) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 29360128) (by decide) (join_sr (m := 293273600) (by decide) (join_su (m := 27262976) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 27262976) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 293273600) (by decide) (join_su (m := 31457280) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 31457280) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (49/160 : ℝ) (233/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  have e3 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
