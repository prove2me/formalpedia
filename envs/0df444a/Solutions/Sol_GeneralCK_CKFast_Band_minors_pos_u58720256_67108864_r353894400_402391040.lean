-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_67108864_r353894400_402391040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:20:21.812489+00:00
-- url     : https://prove2.me/submissions/bf6c8c4e-08c3-4a68-84fa-7fd1322e5d9a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 2/25]`, `ρ ∈ [27/64, 307/640]` by 15 cells of the computing
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
theorem cell0 : cellOK 58720256 60817408 353894400 366018560 ⟨⟨319021414413, 319021414428⟩, ⟨301773880682, 336770175881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 60817408 62914560 353894400 366018560 ⟨⟨314715218237, 314715218252⟩, ⟨297730669035, 332193253931⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 58720256 60817408 366018560 378142720 ⟨⟨326183919221, 326183919236⟩, ⟨308990700734, 343858858979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 60817408 62914560 366018560 378142720 ⟨⟨321855554085, 321855554099⟩, ⟨304918684021, 339267226473⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 62914560 65011712 353894400 366018560 ⟨⟨310501567814, 310501567828⟩, ⟨293772698769, 327716293934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 65011712 67108864 353894400 366018560 ⟨⟨306376692315, 306376692329⟩, ⟨289896526581, 323335201497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 62914560 65011712 366018560 378142720 ⟨⟨317617959694, 317617959708⟩, ⟨300930497471, 334773381643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 65011712 67108864 366018560 378142720 ⟨⟨313467487011, 313467487025⟩, ⟨297022798376, 330373374740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 58720256 60817408 378142720 390266880 ⟨⟨333241197675, 333241197687⟩, ⟨316102261330, 350843082014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 60817408 62914560 378142720 390266880 ⟨⟨328892440389, 328892440404⟩, ⟨312003406767, 346238271743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 58720256 62914560 390266880 402391040 ⟨⟨338003836683, 338003836698⟩, ⟨312515738712, 364530335973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 62914560 65011712 378142720 390266880 ⟨⟨324632701493, 324632701505⟩, ⟨307986974239, 341729120745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 65011712 67108864 378142720 390266880 ⟨⟨320458448069, 320458448084⟩, ⟨304049717623, 337311816351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 62914560 65011712 390266880 402391040 ⟨⟨331550959052, 331550959066⟩, ⟨314947168308, 348588769525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 65011712 67108864 390266880 402391040 ⟨⟨327354584207, 327354584221⟩, ⟨310982163523, 344155633780⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 67108864 353894400 402391040 t = true :=
  ⟨_, (join_sr (m := 378142720) (by decide) (join_su (m := 62914560) (by decide) (join_sr (m := 366018560) (by decide) (join_su (m := 60817408) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 60817408) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 366018560) (by decide) (join_su (m := 65011712) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 65011712) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 62914560) (by decide) (join_sr (m := 390266880) (by decide) (join_su (m := 60817408) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 390266880) (by decide) (join_su (m := 65011712) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 65011712) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (27/64 : ℝ) (307/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  have e3 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
