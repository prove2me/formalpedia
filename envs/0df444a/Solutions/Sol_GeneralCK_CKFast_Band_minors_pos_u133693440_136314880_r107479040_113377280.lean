-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u133693440_136314880_r107479040_113377280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:07:43.509528+00:00
-- url     : https://prove2.me/submissions/b43bd548-0e9e-4b5c-8880-600b6b84eb4a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [51/320, 13/80]`, `ρ ∈ [41/320, 173/1280]` by 13 cells of the computing
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
theorem cell0 : cellOK 133693440 134348800 107479040 108953600 ⟨⟨70606117191, 70606117198⟩, ⟨68481098368, 72749848323⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 133693440 134348800 108953600 110428160 ⟨⟨71501104180, 71501104187⟩, ⟨69373073753, 73647830953⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 134348800 135004160 107479040 108953600 ⟨⟨70280694956, 70280694965⟩, ⟨68163492965, 72416485885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 134348800 135004160 108953600 110428160 ⟨⟨71172075535, 71172075542⟩, ⟨69051869525, 73310854945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 133693440 134348800 110428160 113377280 ⟨⟨72840627801, 72840627807⟩, ⟨70149674068, 75561567552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 134348800 135004160 110428160 113377280 ⟨⟨72506223734, 72506223743⟩, ⟨69826073896, 75216147338⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 135004160 135659520 107479040 108953600 ⟨⟨69957309696, 69957309703⟩, ⟨67847859039, 72085227301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 135004160 135659520 108953600 110428160 ⟨⟨70845100478, 70845100485⟩, ⟨68732653424, 72975999364⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 135659520 136314880 107479040 108953600 ⟨⟨69635938299, 69635938302⟩, ⟨67534174313, 71756048605⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 135659520 136314880 108953600 110428160 ⟨⟨70520155768, 70520155771⟩, ⟨68415403034, 72643240117⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 135004160 135659520 110428160 113377280 ⟨⟨72173897768, 72173897777⟩, ⟨69504464062, 74872895361⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 135659520 136314880 110428160 111902720 ⟨⟨71402849051, 71402849056⟩, ⟨69295119038, 73528895918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 135659520 136314880 111902720 113377280 ⟨⟨72284025620, 72284025622⟩, ⟨70173329713, 74413023553⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 133693440 136314880 107479040 113377280 t = true :=
  ⟨_, (join_su (m := 135004160) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 134348800) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 108953600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 134348800) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 110428160) (by decide) (join_su (m := 135659520) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 108953600) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 135659520) (by decide) (leaf_ok cell10) (join_sr (m := 111902720) (by decide) (leaf_ok cell11) (leaf_ok cell12)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (51/320 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (173/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((133693440 : ℤ) : ℝ) / (D : ℝ)) = (51/320 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
