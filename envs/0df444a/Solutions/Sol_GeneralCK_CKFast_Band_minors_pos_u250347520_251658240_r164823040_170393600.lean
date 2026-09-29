-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u250347520_251658240_r164823040_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T11:27:26.847777+00:00
-- url     : https://prove2.me/submissions/26cfbeba-cc05-4f37-8b48-a8ee88ba3259

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [191/640, 3/10]`, `ρ ∈ [503/2560, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 250347520 250675200 164823040 166215680 ⟨⟨48395842163, 48395842169⟩, ⟨47591946117, 49202611051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 250675200 251002880 164823040 166215680 ⟨⟨48281293563, 48281293568⟩, ⟨47478370938, 49087083593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 250347520 250675200 166215680 167608320 ⟨⟨48793162925, 48793162931⟩, ⟨47988370352, 49600829826⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 250675200 251002880 166215680 167608320 ⟨⟨48677717967, 48677717973⟩, ⟨47873900164, 49484404666⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 251002880 251330560 164823040 166215680 ⟨⟨48166887008, 48166887013⟩, ⟨47364935742, 48971700256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 251330560 251658240 164823040 166215680 ⟨⟨48052621974, 48052621978⟩, ⟨47251640021, 48856460507⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 251002880 251330560 166215680 167608320 ⟨⟨48562415872, 48562415878⟩, ⟨47759570777, 49368124448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 251330560 251658240 166215680 167608320 ⟨⟨48447256119, 48447256120⟩, ⟨47645381680, 49251988635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 250675200 167608320 169000960 ⟨⟨49190333317, 49190333323⟩, ⟨48384644403, 49998898046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250675200 251002880 167608320 169000960 ⟨⟨49073993006, 49073993011⟩, ⟨48269280205, 49881576191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 250675200 169000960 170393600 ⟨⟨49587353676, 49587353682⟩, ⟨48780768603, 50396816045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250675200 251002880 169000960 170393600 ⟨⟨49470119013, 49470119018⟩, ⟨48664511396, 50278598501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 251002880 251330560 167608320 169000960 ⟨⟨48957796372, 48957796377⟩, ⟨48154057623, 49764400094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 251330560 251658240 167608320 169000960 ⟨⟨48841742889, 48841742892⟩, ⟨48038976140, 49647369214⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251330560 169000960 170393600 ⟨⟨49353028836, 49353028841⟩, ⟨48548396610, 50160527525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251330560 251658240 169000960 170393600 ⟨⟨49236082615, 49236082619⟩, ⟨48432423729, 50042602575⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 250347520 251658240 164823040 170393600 t = true :=
  ⟨_, (join_sr (m := 167608320) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 166215680) (by decide) (join_su (m := 250675200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 250675200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 166215680) (by decide) (join_su (m := 251330560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 251330560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 251002880) (by decide) (join_sr (m := 169000960) (by decide) (join_su (m := 250675200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 250675200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 169000960) (by decide) (join_su (m := 251330560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 251330560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (191/640 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (503/2560 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((250347520 : ℤ) : ℝ) / (D : ℝ)) = (191/640 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
