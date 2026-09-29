-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_246415360_r348651520_359792640
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:58:13.276856+00:00
-- url     : https://prove2.me/submissions/55ca31be-7042-4c77-8e1d-38ddccf2eb78

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 47/160]`, `ρ ∈ [133/320, 549/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 242483200 348651520 351436800 ⟨⟨105907095439, 105907095447⟩, ⟨102628090110, 109222809643⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241172480 242483200 351436800 354222080 ⟨⟨106708985897, 106708985904⟩, ⟨103423241327, 110031474278⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 242483200 243793920 348651520 351436800 ⟨⟨104982966978, 104982966985⟩, ⟨101717408818, 108285050545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 242483200 243793920 351436800 354222080 ⟨⟨105778528810, 105778528816⟩, ⟨102506254999, 109087363684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241172480 242483200 354222080 357007360 ⟨⟨107510357395, 107510357402⟩, ⟨104217875364, 110839617996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 241172480 242483200 357007360 359792640 ⟨⟨108311212549, 108311212556⟩, ⟨105011994824, 111647243427⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 242483200 243793920 354222080 357007360 ⟨⟨106573584088, 106573584096⟩, ⟨103294596240, 109889168485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242483200 243793920 357007360 359792640 ⟨⟨107368135358, 107368135365⟩, ⟨104082435071, 110690467506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 243793920 245104640 348651520 351436800 ⟨⟨104062482948, 104062482954⟩, ⟨100810267783, 107351041795⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 243793920 245104640 351436800 354222080 ⟨⟨104851724695, 104851724701⟩, ⟨101592817677, 108147011756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 245104640 246415360 348651520 351436800 ⟨⟨103145595962, 103145595965⟩, ⟨99906620890, 106420734714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 245104640 246415360 351436800 354222080 ⟨⟨103928526139, 103928526142⟩, ⟨100682883209, 107210369794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 243793920 245104640 354222080 357007360 ⟨⟨105640472076, 105640472083⟩, ⟨102374874652, 108942485735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 243793920 245104640 357007360 359792640 ⟨⟨106428727560, 106428727567⟩, ⟨103156441167, 109737466213⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 245104640 246415360 354222080 357007360 ⟨⟨104710973916, 104710973919⟩, ⟨101458664416, 107999521022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 245104640 246415360 357007360 359792640 ⟨⟨105492941691, 105492941693⟩, ⟨102233966897, 108788190811⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 246415360 348651520 359792640 t = true :=
  ⟨_, (join_su (m := 243793920) (by decide) (join_sr (m := 354222080) (by decide) (join_su (m := 242483200) (by decide) (join_sr (m := 351436800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 351436800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 242483200) (by decide) (join_sr (m := 357007360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 357007360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 354222080) (by decide) (join_su (m := 245104640) (by decide) (join_sr (m := 351436800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 351436800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 245104640) (by decide) (join_sr (m := 357007360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 357007360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (47/160 : ℝ) →
    rho ∈ Set.Icc (133/320 : ℝ) (549/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e2 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  have e3 : (((359792640 : ℤ) : ℝ) / (D : ℝ)) = (549/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
