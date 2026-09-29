-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_225443840_r159252480_164823040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T05:10:46.544441+00:00
-- url     : https://prove2.me/submissions/afe26b45-6dce-4b30-9cbc-17ea1087b72f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 43/160]`, `ρ ∈ [243/1280, 503/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 222822400 223477760 159252480 160645120 ⟨⟨56615212891, 56615212897⟩, ⟨55115993284, 58123790330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 222822400 223477760 160645120 162037760 ⟨⟨57091568703, 57091568709⟩, ⟨55590487384, 58602012685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 223477760 224133120 159252480 160645120 ⟨⟨56366268858, 56366268863⟩, ⟨54870352350, 57871509528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223477760 224133120 160645120 162037760 ⟨⟨56840664501, 56840664508⟩, ⟨55342891134, 58347766904⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 223477760 162037760 163430400 ⟨⟨57567666062, 57567666069⟩, ⟨56064723888, 59079975713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222822400 223477760 163430400 164823040 ⟨⟨58043505629, 58043505635⟩, ⟨56538703453, 59557680083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 223477760 224133120 162037760 163430400 ⟨⟨57314804825, 57314804832⟩, ⟨55815175431, 58823768112⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 223477760 224133120 163430400 164823040 ⟨⟨57788690479, 57788690486⟩, ⟨56287205891, 59299513802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 224133120 224788480 159252480 160645120 ⟨⟨56118080736, 56118080738⟩, ⟨54625450463, 57620001732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224133120 224788480 160645120 162037760 ⟨⟨56590520547, 56590520550⟩, ⟨55096038257, 58094298472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224788480 225443840 159252480 160645120 ⟨⟨55870642769, 55870642774⟩, ⟨54381281998, 57369261057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224788480 225443840 160645120 162037760 ⟨⟨56341131056, 56341131062⟩, ⟨54849923104, 57841601477⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224133120 224788480 162037760 163430400 ⟨⟨57062708139, 57062708142⟩, ⟨55566374645, 58568342165⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 224788480 163430400 164823040 ⟨⟨57534644151, 57534644154⟩, ⟨56036460265, 59042133454⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224788480 225443840 162037760 163430400 ⟨⟨56811370192, 56811370199⟩, ⟨55318315852, 58313691939⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224788480 225443840 163430400 164823040 ⟨⟨57281360810, 57281360815⟩, ⟨55786460872, 58785533077⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 225443840 159252480 164823040 t = true :=
  ⟨_, (join_su (m := 224133120) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 223477760) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 160645120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 223477760) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 163430400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 162037760) (by decide) (join_su (m := 224788480) (by decide) (join_sr (m := 160645120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 160645120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 224788480) (by decide) (join_sr (m := 163430400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 163430400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (503/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((164823040 : ℤ) : ℝ) / (D : ℝ)) = (503/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
