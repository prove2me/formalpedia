-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u173015040_178257920_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T00:37:40.849989+00:00
-- url     : https://prove2.me/submissions/59e7919d-49c4-4119-9294-b882ccd92638

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [33/160, 17/80]`, `ρ ∈ [277/1280, 147/640]` by 19 cells of the computing
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
theorem cell0 : cellOK 173015040 174325760 181534720 184320000 ⟨⟨88581222400, 88581222405⟩, ⟨84902082774, 92311336945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 173015040 174325760 184320000 187105280 ⟨⟨89838976493, 89838976498⟩, ⟨86151119915, 93577793436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 174325760 175636480 181534720 184320000 ⟨⟨87850922873, 87850922881⟩, ⟨84192236015, 91560127564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 174325760 175636480 184320000 187105280 ⟨⟨89099627121, 89099627129⟩, ⟨85432255802, 92817503975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 173015040 174325760 187105280 189890560 ⟨⟨91094409371, 91094409376⟩, ⟨87397862117, 94841901953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 173015040 174325760 189890560 192675840 ⟨⟨92347536714, 92347536716⟩, ⟨88642324848, 96103678392⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 174325760 175636480 187105280 189890560 ⟨⟨90346059638, 90346059646⟩, ⟨86670029363, 94072582672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 174325760 175636480 189890560 192675840 ⟨⟨91590235644, 91590235650⟩, ⟨87905571714, 95325379083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 175636480 176291840 181534720 184320000 ⟨⟨87307113891, 87307113899⟩, ⟨85084410065, 89548696685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 176291840 176947200 181534720 184320000 ⟨⟨86946415394, 86946415402⟩, ⟨84730663733, 89180951765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 176947200 184320000 187105280 ⟨⟨88366281487, 88366281493⟩, ⟨84719143428, 92063477491⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 176947200 177602560 181534720 184320000 ⟨⟨86587174983, 86587174990⟩, ⟨84378334426, 88814706740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 177602560 178257920 181534720 184320000 ⟨⟨86229380316, 86229380323⟩, ⟨84027410184, 88449948883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 176947200 177602560 184320000 187105280 ⟨⟨87820151158, 87820151164⟩, ⟨85606551022, 90052429659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 177602560 178257920 184320000 187105280 ⟨⟨87457887993, 87457888001⟩, ⟨85251167912, 89683194132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 176947200 187105280 189890560 ⟨⟨89603758154, 89603758162⟩, ⟨85947993203, 93309570470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 175636480 176947200 189890560 192675840 ⟨⟨90839026389, 90839026395⟩, ⟨87174659100, 94553429992⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 176947200 178257920 187105280 189890560 ⟨⟨88867403129, 88867403136⟩, ⟨85231656483, 92552758766⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 176947200 178257920 189890560 192675840 ⟨⟨90093806742, 90093806749⟩, ⟨86449489417, 93787724143⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 173015040 178257920 181534720 192675840 t = true :=
  ⟨_, (join_su (m := 175636480) (by decide) (join_sr (m := 187105280) (by decide) (join_su (m := 174325760) (by decide) (join_sr (m := 184320000) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 184320000) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 174325760) (by decide) (join_sr (m := 189890560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 189890560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 187105280) (by decide) (join_su (m := 176947200) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 176291840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 184320000) (by decide) (join_su (m := 177602560) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 177602560) (by decide) (leaf_ok cell13) (leaf_ok cell14)))) (join_su (m := 176947200) (by decide) (join_sr (m := 189890560) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_sr (m := 189890560) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (33/160 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((173015040 : ℤ) : ℝ) / (D : ℝ)) = (33/160 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
