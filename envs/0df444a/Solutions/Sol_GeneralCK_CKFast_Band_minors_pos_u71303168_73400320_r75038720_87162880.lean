-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u71303168_73400320_r75038720_87162880
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:29:25.266034+00:00
-- url     : https://prove2.me/submissions/4efb6fd6-6887-4110-acc9-5fdac0cacc87

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/200, 7/80]`, `ρ ∈ [229/2560, 133/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 71303168 71827456 75038720 78069760 ⟨⟨86392030023, 86392030035⟩, ⟨82473770380, 90374629404⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 71827456 72351744 75038720 78069760 ⟨⟨85930672216, 85930672221⟩, ⟨82035002474, 89890005185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 71303168 71827456 78069760 81100800 ⟨⟨89390031639, 89390031651⟩, ⟨85463829329, 93380006610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 71827456 72351744 78069760 81100800 ⟨⟨88916070409, 88916070414⟩, ⟨85012425578, 92882823048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 72351744 72876032 75038720 78069760 ⟨⟨85473826872, 85473826882⟩, ⟨81600476738, 89410174765⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 72876032 73400320 75038720 78069760 ⟨⟨85021421701, 85021421713⟩, ⟨81170125811, 88935060673⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 72351744 72876032 78069760 81100800 ⟨⟨88446702956, 88446702968⟩, ⟨84565347272, 92390512360⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 72876032 73400320 78069760 81100800 ⟨⟨87981856288, 87981856300⟩, ⟨84122526281, 91902996432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 71303168 71827456 81100800 84131840 ⟨⟨92361782380, 92361782392⟩, ⟨88427980122, 96358794964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 71827456 72351744 81100800 84131840 ⟨⟨91875530333, 91875530338⟩, ⟨87964248447, 95849369176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 71303168 71827456 84131840 87162880 ⟨⟨95307805723, 95307805733⟩, ⟨91366733918, 99311530286⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 71827456 72351744 84131840 87162880 ⟨⟨94809565855, 94809565859⟩, ⟨90890972903, 98790169503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 72351744 72876032 81100800 84131840 ⟨⟨91393948806, 91393948819⟩, ⟨87504920989, 95344890699⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 72876032 73400320 81100800 84131840 ⟨⟨90916964183, 90916964195⟩, ⟨87049928923, 94845280872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 72351744 72876032 84131840 87162880 ⟨⟨94316068885, 94316068898⟩, ⟨90419690573, 98273826050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 72876032 73400320 84131840 87162880 ⟨⟨93827240650, 93827240660⟩, ⟨89952817480, 97762420799⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 71303168 73400320 75038720 87162880 t = true :=
  ⟨_, (join_sr (m := 81100800) (by decide) (join_su (m := 72351744) (by decide) (join_sr (m := 78069760) (by decide) (join_su (m := 71827456) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 71827456) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 78069760) (by decide) (join_su (m := 72876032) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 72876032) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 72351744) (by decide) (join_sr (m := 84131840) (by decide) (join_su (m := 71827456) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 71827456) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 84131840) (by decide) (join_su (m := 72876032) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 72876032) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/200 : ℝ) (7/80 : ℝ) →
    rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((71303168 : ℤ) : ℝ) / (D : ℝ)) = (17/200 : ℝ) := by norm_num [D]
  have e1 : (((73400320 : ℤ) : ℝ) / (D : ℝ)) = (7/80 : ℝ) := by norm_num [D]
  have e2 : (((75038720 : ℤ) : ℝ) / (D : ℝ)) = (229/2560 : ℝ) := by norm_num [D]
  have e3 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
