-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u191365120_193986560_r181534720_192675840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:05:22.221886+00:00
-- url     : https://prove2.me/submissions/c1c5eaa8-8ceb-45d3-b2de-e82a660ae74e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [73/320, 37/160]`, `ρ ∈ [277/1280, 147/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 191365120 192020480 181534720 184320000 ⟨⟨79029140592, 79029140595⟩, ⟨76962680483, 81112409201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 192020480 192675840 181534720 184320000 ⟨⟨78700280468, 78700280475⟩, ⟨76639883488, 80777407664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 191365120 192020480 184320000 187105280 ⟨⟨80166291649, 80166291652⟩, ⟨78095294024, 82254093521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 192020480 192675840 184320000 187105280 ⟨⟨79833194781, 79833194789⟩, ⟨77768270777, 81914845074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 192675840 193331200 181534720 184320000 ⟨⟨78372615458, 78372615466⟩, ⟨76318248532, 80443634896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 193331200 193986560 181534720 184320000 ⟨⟨78046135955, 78046135961⟩, ⟨75997766294, 80111080995⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 192675840 193331200 184320000 187105280 ⟨⟨79501302944, 79501302951⟩, ⟨77442419511, 81576835279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 193331200 193986560 184320000 187105280 ⟨⟨79170606472, 79170606478⟩, ⟨77117730845, 81240054185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 191365120 192020480 187105280 189890560 ⟨⟨81301723777, 81301723780⟩, ⟨79226200105, 83394047323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 192020480 192675840 187105280 189890560 ⟨⟨80964409160, 80964409166⟩, ⟨78894969419, 83050571141⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 191365120 192020480 189890560 192675840 ⟨⟨82435447414, 82435447415⟩, ⟨80355409081, 84532281126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 192020480 192675840 189890560 192675840 ⟨⟨82093933884, 82093933890⟩, ⟨80019989614, 84184596228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 192675840 193331200 187105280 189890560 ⟨⟨80628309300, 80628309306⟩, ⟨78564920469, 82708343307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 193331200 193986560 187105280 189890560 ⟨⟨80293414485, 80293414491⟩, ⟨78236043825, 82367353823⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 192675840 193331200 189890560 192675840 ⟨⟨81753644659, 81753644665⟩, ⟨79685761457, 83838169193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 193331200 193986560 189890560 192675840 ⟨⟨81414569975, 81414569981⟩, ⟨79352715135, 83492989969⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 191365120 193986560 181534720 192675840 t = true :=
  ⟨_, (join_sr (m := 187105280) (by decide) (join_su (m := 192675840) (by decide) (join_sr (m := 184320000) (by decide) (join_su (m := 192020480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 192020480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 184320000) (by decide) (join_su (m := 193331200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 193331200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 192675840) (by decide) (join_sr (m := 189890560) (by decide) (join_su (m := 192020480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 192020480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 189890560) (by decide) (join_su (m := 193331200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 193331200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (73/320 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (277/1280 : ℝ) (147/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  have e3 : (((192675840 : ℤ) : ℝ) / (D : ℝ)) = (147/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
