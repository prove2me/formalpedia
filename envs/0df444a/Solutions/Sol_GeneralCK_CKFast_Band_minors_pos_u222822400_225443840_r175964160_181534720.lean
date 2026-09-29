-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_225443840_r175964160_181534720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:43:28.038113+00:00
-- url     : https://prove2.me/submissions/f042a32e-299a-4fae-9c94-f68d6bc7251f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 43/160]`, `ρ ∈ [537/2560, 277/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 222822400 223477760 175964160 177356800 ⟨⟨62314569345, 62314569351⟩, ⟨60793065211, 63845488303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 222822400 223477760 177356800 178749440 ⟨⟨62787866992, 62787866998⟩, ⟨61264511274, 64320642191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 223477760 224133120 175964160 177356800 ⟨⟨62042307824, 62042307830⟩, ⟨60524163600, 63569833714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223477760 224133120 177356800 178749440 ⟨⟨62513682229, 62513682234⟩, ⟨60993691017, 64043059804⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 223477760 178749440 180142080 ⟨⟨63260914014, 63260914020⟩, ⟨61735707541, 64795544607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222822400 223477760 180142080 181534720 ⟨⟨63733711052, 63733711057⟩, ⟨62206654650, 65270196198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 223477760 224133120 178749440 180142080 ⟨⟨62984809019, 62984809024⟩, ⟨61462971629, 64516037456⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 223477760 224133120 180142080 181534720 ⟨⟨63455688827, 63455688833⟩, ⟨61932006066, 64988767305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 224133120 224788480 175964160 177356800 ⟨⟨61770852161, 61770852163⟩, ⟨60256050914, 63295002132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224133120 224788480 177356800 178749440 ⟨⟨62240307282, 62240307285⟩, ⟨60723663644, 63766304388⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224788480 225443840 175964160 177356800 ⟨⟨61500196299, 61500196305⟩, ⟨59988721234, 63020987376⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224788480 225443840 177356800 178749440 ⟨⟨61967736078, 61967736084⟩, ⟨60454423212, 63490369740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224133120 224788480 178749440 180142080 ⟨⟨62709517773, 62709517775⟩, ⟨61191032531, 64237361209⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 224788480 180142080 181534720 ⟨⟨63178484253, 63178484255⟩, ⟨61658158194, 64708173219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224788480 225443840 178749440 180142080 ⟨⟨62435034176, 62435034183⟩, ⟨60919884277, 63959509641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224788480 225443840 180142080 181534720 ⟨⟨62902091208, 62902091213⟩, ⟨61385105042, 64428407694⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 225443840 175964160 181534720 t = true :=
  ⟨_, (join_su (m := 224133120) (by decide) (join_sr (m := 178749440) (by decide) (join_su (m := 223477760) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 177356800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 223477760) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 180142080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 178749440) (by decide) (join_su (m := 224788480) (by decide) (join_sr (m := 177356800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 177356800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 224788480) (by decide) (join_sr (m := 180142080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 180142080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (537/2560 : ℝ) (277/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  have e3 : (((181534720 : ℤ) : ℝ) / (D : ℝ)) = (277/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
