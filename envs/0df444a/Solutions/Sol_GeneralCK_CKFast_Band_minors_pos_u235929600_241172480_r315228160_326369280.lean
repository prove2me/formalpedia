-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r315228160_326369280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:35:57.495637+00:00
-- url     : https://prove2.me/submissions/b4f21766-c0f9-4e05-91ae-34a79697bb5c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [481/1280, 249/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 315228160 318013440 ⟨⟨99667923063, 99667923069⟩, ⟨96416238668, 102956670690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 237240320 318013440 320798720 ⟨⟨100502296851, 100502296857⟩, ⟨97243749820, 103797941279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 238551040 315228160 318013440 ⟨⟨98806157014, 98806157019⟩, ⟨95568062538, 102081114861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 318013440 320798720 ⟨⟨99634001290, 99634001297⟩, ⟨96389069153, 102915831708⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 237240320 320798720 323584000 ⟨⟨101336063778, 101336063784⟩, ⟨98070656807, 104638602122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 237240320 323584000 326369280 ⟨⟨102169226903, 102169226910⟩, ⟨98896962671, 105478656295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 238551040 320798720 323584000 ⟨⟨100461253049, 100461253055⟩, ⟨97209485751, 103749953348⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237240320 238551040 323584000 326369280 ⟨⟨101287915259, 101287915265⟩, ⟨98029315286, 104583482770⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239861760 315228160 318013440 ⟨⟨97948108496, 97948108498⟩, ⟨94723492006, 101209390556⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238551040 239861760 318013440 320798720 ⟨⟨98769434875, 98769434880⟩, ⟨95538005881, 102037565072⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 241172480 315228160 318013440 ⟨⟨97093728105, 97093728111⟩, ⟨93882479108, 100341446911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 241172480 318013440 320798720 ⟨⟨97908548139, 97908548147⟩, ⟨94690511970, 101163090453⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 320798720 323584000 ⟨⟨99590182820, 99590182824⟩, ⟨96351943632, 102865158660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238551040 239861760 323584000 326369280 ⟨⟨100410355214, 100410355218⟩, ⟨97165308128, 103692174220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 241172480 320798720 323584000 ⟨⟨98722803566, 98722803573⟩, ⟨95497982349, 101984167084⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 323584000 326369280 ⟨⟨99536497186, 99536497193⟩, ⟨96304893034, 102804679621⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 315228160 326369280 t = true :=
  ⟨_, (join_su (m := 238551040) (by decide) (join_sr (m := 320798720) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 318013440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 237240320) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 323584000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 320798720) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 318013440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 318013440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 239861760) (by decide) (join_sr (m := 323584000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 323584000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (481/1280 : ℝ) (249/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((315228160 : ℤ) : ℝ) / (D : ℝ)) = (481/1280 : ℝ) := by norm_num [D]
  have e3 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
