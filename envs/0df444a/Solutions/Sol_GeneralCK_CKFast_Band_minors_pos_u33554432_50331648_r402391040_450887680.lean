-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r402391040_450887680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:53:57.508857+00:00
-- url     : https://prove2.me/submissions/996f07ae-70d7-4153-82ab-9e2c5b1ad606

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/25, 3/50]`, `ρ ∈ [307/640, 43/80]` by 16 cells of the computing
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
theorem cell0 : cellOK 33554432 37748736 402391040 414515200 ⟨⟨405029518105, 405029518123⟩, ⟨374654585385, 436503870135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 33554432 37748736 414515200 426639360 ⟨⟨411823157630, 411823157647⟩, ⟨381627227152, 443060771834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 37748736 41943040 402391040 414515200 ⟨⟨393774439261, 393774439275⟩, ⟨364361786750, 424276068381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 37748736 41943040 414515200 426639360 ⟨⟨400591638617, 400591638633⟩, ⟨371328510883, 430890314578⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 33554432 37748736 426639360 438763520 ⟨⟨418521981128, 418521981145⟩, ⟨388500400892, 449530138092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 33554432 37748736 438763520 450887680 ⟨⟨425131442885, 425131442899⟩, ⟨395279665183, 455917132327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 37748736 41943040 426639360 438763520 ⟨⟨407314805321, 407314805339⟩, ⟨378197749744, 437416270501⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 37748736 41943040 438763520 450887680 ⟨⟨413949218018, 413949218031⟩, ⟨384974818905, 443859022564⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 41943040 46137344 402391040 414515200 ⟨⟨383076039721, 383076039737⟩, ⟨354559588809, 412667333049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 41943040 46137344 414515200 426639360 ⟨⟨389903417325, 389903417342⟩, ⟨361510129010, 419322109320⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 46137344 50331648 402391040 414515200 ⟨⟨372878773877, 372878773893⟩, ⟨345200921391, 401614885971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 46137344 50331648 414515200 426639360 ⟨⟨379704693991, 379704694006⟩, ⟨352126367177, 408295536700⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 41943040 46137344 426639360 438763520 ⟨⟨396638030317, 396638030332⟩, ⟨368365453082, 425888564300⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 41943040 46137344 438763520 450887680 ⟨⟨403284960783, 403284960799⟩, ⟨375130628290, 432371665861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 46137344 50331648 426639360 438763520 ⟨⟨386439499632, 386439499647⟩, ⟨358959081529, 414888419709⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 46137344 50331648 438763520 450887680 ⟨⟨393088062970, 393088062985⟩, ⟨365703882494, 421398354269⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 33554432 50331648 402391040 450887680 t = true :=
  ⟨_, (join_su (m := 41943040) (by decide) (join_sr (m := 426639360) (by decide) (join_su (m := 37748736) (by decide) (join_sr (m := 414515200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 414515200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 37748736) (by decide) (join_sr (m := 438763520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 438763520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 426639360) (by decide) (join_su (m := 46137344) (by decide) (join_sr (m := 414515200) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 414515200) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 46137344) (by decide) (join_sr (m := 438763520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 438763520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (307/640 : ℝ) (43/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((402391040 : ℤ) : ℝ) / (D : ℝ)) = (307/640 : ℝ) := by norm_num [D]
  have e3 : (((450887680 : ℤ) : ℝ) / (D : ℝ)) = (43/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
