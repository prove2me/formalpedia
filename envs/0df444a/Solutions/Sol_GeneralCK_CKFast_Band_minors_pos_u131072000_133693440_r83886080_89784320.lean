-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_133693440_r83886080_89784320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:53:21.436928+00:00
-- url     : https://prove2.me/submissions/ac536d42-5d17-4948-b82d-438861c7c13a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 51/320]`, `ρ ∈ [1/10, 137/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 131072000 131727360 83886080 85360640 ⟨⟨57143365403, 57143365410⟩, ⟨55036880101, 59269346346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 131072000 131727360 85360640 86835200 ⟨⟨58080596247, 58080596256⟩, ⟨55970852740, 60209818685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131727360 132382720 83886080 85360640 ⟨⟨56871075218, 56871075225⟩, ⟨54772531266, 58988978279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 131727360 132382720 85360640 86835200 ⟨⟨57804304426, 57804304435⟩, ⟨55702512981, 59925438731⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131072000 131727360 86835200 88309760 ⟨⟨59016030910, 59016030918⟩, ⟨56903043496, 61148480472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 131072000 131727360 88309760 89784320 ⟨⟨59949678761, 59949678769⟩, ⟨57833461631, 62085341183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131727360 132382720 86835200 88309760 ⟨⟨58735759099, 58735759106⟩, ⟨56630734236, 60860110497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 131727360 132382720 88309760 89784320 ⟨⟨59665448440, 59665448449⟩, ⟨57557204133, 61793002890⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 132382720 133038080 83886080 85360640 ⟨⟨56600609099, 56600609103⟩, ⟨54509937272, 58710505117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 132382720 133038080 85360640 86835200 ⟨⟨57529857988, 57529857993⟩, ⟨55435949373, 59642974998⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133038080 133693440 83886080 85360640 ⟨⟨56331945212, 56331945218⟩, ⟨54249077208, 58433904091⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 133038080 133693440 85360640 86835200 ⟨⟨57257234896, 57257234904⟩, ⟨55171140799, 59362404514⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 132382720 133038080 86835200 88309760 ⟨⟨58457353705, 58457353710⟩, ⟨56360222158, 60573677777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 132382720 133038080 88309760 89784320 ⟨⟨59383105294, 59383105299⟩, ⟨57282764572, 61502622601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 133038080 133693440 86835200 88309760 ⟨⟨58180792496, 58180792502⟩, ⟨56091485947, 60289159140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133038080 133693440 88309760 89784320 ⟨⟨59102626895, 59102626904⟩, ⟨57010121440, 61214176950⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 133693440 83886080 89784320 t = true :=
  ⟨_, (join_su (m := 132382720) (by decide) (join_sr (m := 86835200) (by decide) (join_su (m := 131727360) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 85360640) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 131727360) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 88309760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 86835200) (by decide) (join_su (m := 133038080) (by decide) (join_sr (m := 85360640) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 85360640) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 133038080) (by decide) (join_sr (m := 88309760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 88309760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (51/320 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((133693440 : ℤ) : ℝ) / (D : ℝ)) = (51/320 : ℝ) := by norm_num [D]
  have e2 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e3 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
