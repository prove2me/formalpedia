-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_222822400_r170393600_175964160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:39:31.153327+00:00
-- url     : https://prove2.me/submissions/6a40d182-98de-4809-847d-61531af530d2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 17/64]`, `ρ ∈ [13/64, 537/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 220200960 220856320 170393600 171786240 ⟨⟨61485030490, 61485030496⟩, ⟨59957404054, 63022188609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 220856320 171786240 173178880 ⟨⟨61967119972, 61967119979⟩, ⟨60437619843, 63506156320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 220856320 221511680 170393600 171786240 ⟨⟨61217272845, 61217272848⟩, ⟨59693056681, 62750986436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 220856320 221511680 171786240 173178880 ⟨⟨61697410362, 61697410365⟩, ⟨60171325203, 63232997528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 220856320 173178880 174571520 ⟨⟨62448943726, 62448943731⟩, ⟨60917570828, 63989857361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 220200960 220856320 174571520 175964160 ⟨⟨62930502438, 62930502444⟩, ⟨61397257693, 64473292424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 220856320 221511680 173178880 174571520 ⟨⟨62177285327, 62177285329⟩, ⟨60649332076, 63714745150⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 220856320 221511680 174571520 175964160 ⟨⟨62656898418, 62656898421⟩, ⟨61127077974, 64196229983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 221511680 222167040 170393600 171786240 ⟨⟨60950329248, 60950329255⟩, ⟨59429505919, 62480615989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 221511680 222167040 171786240 173178880 ⟨⟨61428518980, 61428518987⟩, ⟨59905831349, 62960674646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222167040 222822400 170393600 171786240 ⟨⟨60684193538, 60684193545⟩, ⟨59166745733, 62211070964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 222167040 222822400 171786240 173178880 ⟨⟨61160439640, 61160439645⟩, ⟨59641132223, 62689181347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 221511680 222167040 173178880 174571520 ⟨⟨61906449305, 61906449311⟩, ⟨60381898253, 63440473001⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 221511680 222167040 174571520 175964160 ⟨⟨62384120891, 62384120897⟩, ⟨60857707299, 63920011723⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 222167040 222822400 173178880 174571520 ⟨⟨61636429449, 61636429455⟩, ⟨60115263281, 63167034561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 222167040 222822400 174571520 175964160 ⟨⟨62112163623, 62112163630⟩, ⟨60589139562, 63644631270⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 222822400 170393600 175964160 t = true :=
  ⟨_, (join_su (m := 221511680) (by decide) (join_sr (m := 173178880) (by decide) (join_su (m := 220856320) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 171786240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 220856320) (by decide) (join_sr (m := 174571520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 174571520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 173178880) (by decide) (join_su (m := 222167040) (by decide) (join_sr (m := 171786240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 171786240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 222167040) (by decide) (join_sr (m := 174571520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 174571520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (17/64 : ℝ) →
    rho ∈ Set.Icc (13/64 : ℝ) (537/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e2 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  have e3 : (((175964160 : ℤ) : ℝ) / (D : ℝ)) = (537/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
