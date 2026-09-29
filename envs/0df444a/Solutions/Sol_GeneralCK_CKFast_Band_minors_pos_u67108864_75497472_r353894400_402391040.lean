-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_75497472_r353894400_402391040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:56:27.390479+00:00
-- url     : https://prove2.me/submissions/bab00dcf-6d46-468a-b5f7-37baddba6c91

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 9/100]`, `ρ ∈ [27/64, 307/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 69206016 353894400 366018560 ⟨⟨302337048275, 302337048289⟩, ⟨286098914855, 319046130256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 69206016 71303168 353894400 366018560 ⟨⟨298379300516, 298379300530⟩, ⟨282376814574, 314845460993⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 67108864 69206016 366018560 378142720 ⟨⟨309400705572, 309400705586⟩, ⟨293192442397, 326063493708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69206016 71303168 366018560 378142720 ⟨⟨305414385161, 305414385172⟩, ⟨289436467107, 321840244166⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 71303168 73400320 353894400 366018560 ⟨⟨294500305180, 294500305192⟩, ⟨278727350152, 310729782973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 73400320 75497472 353894400 366018560 ⟨⟨290697094538, 290697094549⟩, ⟨275147805823, 306695877321⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 71303168 73400320 366018560 378142720 ⟨⟨301505479506, 301505479519⟩, ⟨285752077367, 317700331535⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 73400320 75497472 366018560 378142720 ⟨⟨297671111703, 297671111716⟩, ⟨282136632227, 313640645130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 67108864 69206016 378142720 390266880 ⟨⟨316366357592, 316366357604⟩, ⟨300188582314, 332982773980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 69206016 71303168 378142720 390266880 ⟨⟨312353300260, 312353300271⟩, ⟨296400689307, 328738617950⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 67108864 69206016 390266880 402391040 ⟨⟨323238858873, 323238858887⟩, ⟨307092057618, 339808929431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 69206016 71303168 390266880 402391040 ⟨⟨319200749293, 319200749306⟩, ⟨303274051916, 335545393644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 71303168 73400320 378142720 390266880 ⟨⟨308416323332, 308416323346⟩, ⟨292683321123, 324576164310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 73400320 75497472 378142720 390266880 ⟨⟨304552637098, 304552637111⟩, ⟨289033909153, 320492405581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 71303168 73400320 390266880 402391040 ⟨⟨315237392316, 315237392329⟩, ⟨299525503813, 331361947821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 73400320 75497472 390266880 402391040 ⟨⟨311346081883, 311346081897⟩, ⟨295843914584, 327255682912⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 75497472 353894400 402391040 t = true :=
  ⟨_, (join_sr (m := 378142720) (by decide) (join_su (m := 71303168) (by decide) (join_sr (m := 366018560) (by decide) (join_su (m := 69206016) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 69206016) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 366018560) (by decide) (join_su (m := 73400320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 73400320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 71303168) (by decide) (join_sr (m := 390266880) (by decide) (join_su (m := 69206016) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 69206016) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 390266880) (by decide) (join_su (m := 73400320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 73400320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (27/64 : ℝ) (307/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((353894400 : ℤ) : ℝ) / (D : ℝ)) = (27/64 : ℝ) := by norm_num [D]
  have e3 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
