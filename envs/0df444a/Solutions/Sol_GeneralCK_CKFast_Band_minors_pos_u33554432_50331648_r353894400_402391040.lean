-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r353894400_402391040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:53:02.317846+00:00
-- url     : https://prove2.me/submissions/d5955468-82d5-4778-8fc7-a812513d7086

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 3/50]`, `ρ ∈ [27/64, 307/640]` by 18 cells of the computing
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
theorem cell0 : cellOK 33554432 37748736 353894400 366018560 ⟨⟨376782427020, 376782427035⟩, ⟨345643119089, 409282769422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 33554432 37748736 366018560 378142720 ⟨⟨384018747838, 384018747855⟩, ⟨353077948759, 416250084510⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 37748736 41943040 353894400 366018560 ⟨⟨365445429200, 365445429217⟩, ⟨335399817902, 396820245794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 37748736 41943040 366018560 378142720 ⟨⟨372699850472, 372699850489⟩, ⟨342817704007, 403846764659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 33554432 37748736 378142720 390266880 ⟨⟨391133880615, 391133880631⟩, ⟨360386599714, 423104773348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 33554432 37748736 390266880 402391040 ⟨⟨398135198127, 398135198144⟩, ⟨367576512340, 429853871418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 37748736 41943040 378142720 390266880 ⟨⟨379834865469, 379834865486⟩, ⟨350112710388, 410760414325⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 37748736 41943040 390266880 402391040 ⟨⟨386857543825, 386857543842⟩, ⟨357291887017, 417568064373⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 41943040 44040192 353894400 366018560 ⟨⟨357350267846, 357350267863⟩, ⟨337687188889, 377579524104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 44040192 46137344 353894400 366018560 ⟨⟨352131993080, 352131993096⟩, ⟨332805705352, 372016173646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 41943040 46137344 366018560 378142720 ⟨⟨361980899427, 361980899443⟩, ⟨333080610816, 392117754821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 46137344 48234496 353894400 366018560 ⟨⟨347047945227, 347047945243⟩, ⟨328047364220, 366598143435⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 48234496 50331648 353894400 366018560 ⟨⟨342091442146, 342091442162⟩, ⟨323406111002, 361318147917⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 46137344 50331648 366018560 378142720 ⟨⟨351800410602, 351800410617⟩, ⟨323815058855, 380992831116⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 41943040 46137344 378142720 390266880 ⟨⟨369120832335, 369120832348⟩, ⟨340350828631, 399071102029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 41943040 46137344 390266880 402391040 ⟨⟨376150456400, 376150456416⟩, ⟨347508419228, 405918906260⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 46137344 50331648 378142720 390266880 ⟨⟨358932402740, 358932402756⟩, ⟨331050941316, 387969270868⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 46137344 50331648 390266880 402391040 ⟨⟨365956533644, 365956533660⟩, ⟨338177607511, 394841308195⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 50331648 353894400 402391040 t = true :=
  ⟨_, (join_su (m := 41943040) (by decide) (join_sr (m := 378142720) (by decide) (join_su (m := 37748736) (by decide) (join_sr (m := 366018560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 366018560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 37748736) (by decide) (join_sr (m := 390266880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 390266880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 378142720) (by decide) (join_su (m := 46137344) (by decide) (join_sr (m := 366018560) (by decide) (join_su (m := 44040192) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 366018560) (by decide) (join_su (m := 48234496) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))) (join_su (m := 46137344) (by decide) (join_sr (m := 390266880) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 390266880) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (27/64 : ℝ) (307/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  have e3 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
