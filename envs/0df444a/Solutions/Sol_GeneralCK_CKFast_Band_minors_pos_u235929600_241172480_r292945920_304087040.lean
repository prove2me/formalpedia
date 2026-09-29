-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r292945920_304087040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:15:08.768593+00:00
-- url     : https://prove2.me/submissions/458fa8f5-6904-483c-923a-aad132da3b50

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [447/1280, 29/80]` by 19 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 292945920 295731200 ⟨⟨92970715122, 92970715129⟩, ⟨89774030929, 96204182424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 237240320 295731200 298516480 ⟨⟨93810055231, 93810055237⟩, ⟨90606486216, 97050443031⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 238551040 292945920 295731200 ⟨⟨92161712053, 92161712060⟩, ⟨88978410881, 95381590711⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 295731200 298516480 ⟨⟨92994404729, 92994404735⟩, ⟨89804245296, 96221178024⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 237240320 298516480 301301760 ⟨⟨94648763610, 94648763616⟩, ⟨91438312604, 97896068885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 237240320 301301760 304087040 ⟨⟨95486843407, 95486843413⟩, ⟨92269513228, 98741063152⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 238551040 298516480 301301760 ⟨⟨93826480728, 93826480735⟩, ⟨90629465667, 97060145849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237240320 238551040 301301760 304087040 ⟨⟨94657943111, 94657943117⟩, ⟨91454075037, 97898497256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239206400 292945920 295731200 ⟨⟨91557334792, 91557334799⟩, ⟨89708608787, 93418789777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 239206400 239861760 292945920 295731200 ⟨⟨91155536121, 91155536127⟩, ⟨89311438569, 93012319543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 239861760 295731200 298516480 ⟨⟨92182383020, 92182383025⟩, ⟨89005520081, 95395657092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 240517120 292945920 295731200 ⟨⟨90754625986, 90754625993⟩, ⟨88915138431, 92606756529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 240517120 241172480 292945920 295731200 ⟨⟨90354598381, 90354598384⟩, ⟨88519702485, 92202094601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 240517120 295731200 298516480 ⟨⟨91575718721, 91575718728⟩, ⟨89732579916, 93431508531⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 240517120 241172480 295731200 298516480 ⟨⟨91172384519, 91172384522⟩, ⟨89333845344, 93023532167⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 238551040 239861760 298516480 301301760 ⟨⟨93007840131, 93007840135⟩, ⟨89824148076, 96227980204⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 238551040 239861760 301301760 304087040 ⟨⟨93832698315, 93832698316⟩, ⟨90642179561, 97059701791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 239861760 241172480 298516480 301301760 ⟨⟨92192792872, 92192792879⟩, ⟨89022312360, 95399521511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 239861760 241172480 301301760 304087040 ⟨⟨93011059984, 93011059990⟩, ⟨89833779241, 96224626237⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 292945920 304087040 t = true :=
  ⟨_, (join_su (m := 238551040) (by decide) (join_sr (m := 298516480) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 295731200) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 295731200) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 237240320) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 301301760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 298516480) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 295731200) (by decide) (join_su (m := 239206400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 295731200) (by decide) (join_su (m := 240517120) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 240517120) (by decide) (leaf_ok cell13) (leaf_ok cell14)))) (join_su (m := 239861760) (by decide) (join_sr (m := 301301760) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_sr (m := 301301760) (by decide) (leaf_ok cell17) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (447/1280 : ℝ) (29/80 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((292945920 : ℤ) : ℝ) / (D : ℝ)) = (447/1280 : ℝ) := by norm_num [D]
  have e3 : (((304087040 : ℤ) : ℝ) / (D : ℝ)) = (29/80 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
