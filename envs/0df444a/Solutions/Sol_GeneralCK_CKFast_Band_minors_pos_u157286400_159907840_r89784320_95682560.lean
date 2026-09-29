-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_159907840_r89784320_95682560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:14:06.175188+00:00
-- url     : https://prove2.me/submissions/61af6d35-19a5-4946-9893-848c704f39c2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 61/320]`, `ρ ∈ [137/1280, 73/640]` by 20 cells of the computing
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
theorem cell0 : cellOK 157286400 157614080 89784320 91258880 ⟨⟨50704789515, 50704789522⟩, ⟨49548462382, 51867084452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 157614080 157941760 89784320 91258880 ⟨⟨50591219942, 50591219947⟩, ⟨49436929135, 51751459553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 157941760 91258880 92733440 ⟨⟨51435533744, 51435533752⟩, ⟨49586350544, 53299778174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 157941760 158269440 89784320 91258880 ⟨⟨50477958852, 50477958853⟩, ⟨49325697131, 51636150472⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 158269440 158597120 89784320 91258880 ⟨⟨50365004650, 50365004656⟩, ⟨49214764818, 51521155581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 157941760 158597120 91258880 92733440 ⟨⟨51205777321, 51205777327⟩, ⟨49362397260, 53064131817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 157286400 157941760 92733440 94208000 ⟨⟨52222006604, 52222006610⟩, ⟨50370015832, 54089054476⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 157286400 157941760 94208000 95682560 ⟨⟨53007389240, 53007389246⟩, ⟨51152598297, 54877233108⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157941760 158597120 92733440 94208000 ⟨⟨51989029132, 51989029139⟩, ⟨50142850652, 53850178136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 157941760 158597120 94208000 95682560 ⟨⟨52771203443, 52771203450⟩, ⟨50922233827, 54635139618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 158597120 158924800 89784320 91258880 ⟨⟨50252355765, 50252355771⟩, ⟨49104130662, 51406473254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 158924800 159252480 89784320 91258880 ⟨⟨50140010624, 50140010630⟩, ⟨48993793129, 51292101887⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 158597120 159252480 91258880 92733440 ⟨⟨50977259500, 50977259503⟩, ⟨49139640089, 52829767417⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 159252480 159580160 89784320 91258880 ⟨⟨50027967669, 50027967675⟩, ⟨48883750702, 51178039879⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 159580160 159907840 89784320 91258880 ⟨⟨49916225354, 49916225355⟩, ⟨48774001878, 51064285641⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 159252480 159907840 91258880 92733440 ⟨⟨50749967606, 50749967612⟩, ⟨48918066835, 52596671821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 158597120 159252480 92733440 94208000 ⟨⟨51757304298, 51757304301⟩, ⟨49916895596, 53612597807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 158597120 159252480 94208000 95682560 ⟨⟨52536284166, 52536284169⟩, ⟨50693093339, 54394356044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 159252480 159907840 92733440 94208000 ⟨⟨51526819307, 51526819313⟩, ⟨49692138345, 53376300215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 159252480 159907840 94208000 95682560 ⟨⟨52302618499, 52302618505⟩, ⟨50465164402, 54154868993⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 159907840 89784320 95682560 t = true :=
  ⟨_, (join_su (m := 158597120) (by decide) (join_sr (m := 92733440) (by decide) (join_su (m := 157941760) (by decide) (join_sr (m := 91258880) (by decide) (join_su (m := 157614080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 91258880) (by decide) (join_su (m := 158269440) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (leaf_ok cell5))) (join_su (m := 157941760) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 94208000) (by decide) (leaf_ok cell8) (leaf_ok cell9)))) (join_sr (m := 92733440) (by decide) (join_su (m := 159252480) (by decide) (join_sr (m := 91258880) (by decide) (join_su (m := 158924800) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12)) (join_sr (m := 91258880) (by decide) (join_su (m := 159580160) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (leaf_ok cell15))) (join_su (m := 159252480) (by decide) (join_sr (m := 94208000) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (join_sr (m := 94208000) (by decide) (leaf_ok cell18) (leaf_ok cell19)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (61/320 : ℝ) →
    rho ∈ Set.Icc (137/1280 : ℝ) (73/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e2 : (((89784320 : ℤ) : ℝ) / (D : ℝ)) = (137/1280 : ℝ) := by norm_num [D]
  have e3 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
