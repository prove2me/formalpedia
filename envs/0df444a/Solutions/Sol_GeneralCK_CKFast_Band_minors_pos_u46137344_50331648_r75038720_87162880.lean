-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u46137344_50331648_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:42:44.971071+00:00
-- url     : https://prove2.me/submissions/3e241023-4dea-433e-aa51-bb9eb6f16b5d

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/200, 3/50]`, `ρ ∈ [229/2560, 133/1280]` by 18 cells of the computing
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
theorem cell0 : cellOK 46137344 47185920 75038720 78069760 ⟨⟨115404773478, 115404773494⟩, ⟨107548080425, 123510130859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 46137344 47185920 78069760 81100800 ⟨⟨119108066047, 119108066064⟩, ⟨111244900599, 127216480805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 47185920 48234496 75038720 78069760 ⟨⟨113807083934, 113807083950⟩, ⟨106074849459, 121780955719⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 47185920 48234496 78069760 81100800 ⟨⟨117476079030, 117476079043⟩, ⟨109736638020, 125453922421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 46137344 47185920 81100800 84131840 ⟨⟨122762852258, 122762852271⟩, ⟨114894155812, 130873438135⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 46137344 47185920 84131840 87162880 ⟨⟨126370505386, 126370505403⟩, ⟨118497166298, 134482428586⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 47185920 48234496 81100800 84131840 ⟨⟨121097901608, 121097901624⟩, ⟨113352172411, 129078848682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 47185920 48234496 84131840 87162880 ⟨⟨124673865153, 124673865166⟩, ⟨116922715652, 132657097949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 48234496 48758784 75038720 78069760 ⟨⟨112637498550, 112637498566⟩, ⟨107353091879, 118032400790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 48758784 49283072 75038720 78069760 ⟨⟨111870983715, 111870983727⟩, ⟨106628702862, 117222191197⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 48234496 49283072 78069760 81100800 ⟨⟨115888057783, 115888057798⟩, ⟨108268211211, 123739759654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 49283072 49807360 75038720 78069760 ⟨⟨111114767794, 111114767810⟩, ⟨105913917063, 116423010705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 49807360 50331648 75038720 78069760 ⟨⟨110368628636, 110368628651⟩, ⟨105208529586, 115634618873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 49283072 50331648 78069760 81100800 ⟨⟨114342115502, 114342115518⟩, ⟨106837937725, 122071883762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 48234496 49283072 81100800 84131840 ⟨⟨119477291489, 119477291505⟩, ⟨111850460652, 127332957293⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 48234496 49283072 84131840 87162880 ⟨⟨123021897523, 123021897536⟩, ⟨115388929845, 130880725551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 49283072 50331648 81100800 84131840 ⟨⟨117899138438, 117899138450⟩, ⟨110387336578, 125633664276⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 49283072 50331648 84131840 87162880 ⟨⟨121412724044, 121412724060⟩, ⟨113894125163, 129151222303⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 46137344 50331648 75038720 87162880 t = true :=
  ⟨_, (join_su (m := 48234496) (by decide) (join_sr (m := 81100800) (by decide) (join_su (m := 47185920) (by decide) (join_sr (m := 78069760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 78069760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 47185920) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 84131840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 81100800) (by decide) (join_su (m := 49283072) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 48758784) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 78069760) (by decide) (join_su (m := 49807360) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))) (join_su (m := 49283072) (by decide) (join_sr (m := 84131840) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 84131840) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/200 : ℝ) (3/50 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((46137344 : ℤ) : ℝ) / (D : ℝ)) = (11/200 : ℝ) := by norm_num [D]
  have e1 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
