-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_241172480_r749731840_772014080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T15:08:02.388248+00:00
-- url     : https://prove2.me/submissions/33ca196a-f18e-4fe9-8247-59d60704dfae

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/40, 23/80]`, `ρ ∈ [143/160, 589/640]` by 19 cells of the computing
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
theorem cell0 : cellOK 230686720 233308160 749731840 755302400 ⟨⟨230729543102, 230729543111⟩, ⟨222052721146, 239566287377⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 230686720 233308160 755302400 760872960 ⟨⟨232307315027, 232307315036⟩, ⟨223603885418, 241170623972⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 235929600 749731840 755302400 ⟨⟨227199104623, 227199104632⟩, ⟨218585373306, 235972509861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233308160 235929600 755302400 760872960 ⟨⟨228756523277, 228756523285⟩, ⟨220116207434, 237556492805⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 230686720 233308160 760872960 766443520 ⟨⟨233884123794, 233884123805⟩, ⟨225154088982, 242773990560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 230686720 233308160 766443520 772014080 ⟨⟨235459986540, 235459986547⟩, ⟨226703348677, 244376404544⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 233308160 235929600 760872960 766443520 ⟨⟨230313017071, 230313017079⟩, ⟨221646117762, 239139545548⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 233308160 235929600 766443520 772014080 ⟨⟨231868602391, 231868602399⟩, ⟨223175120402, 240721684726⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 238551040 749731840 755302400 ⟨⟨223682705442, 223682705451⟩, ⟨215131659828, 232393161493⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 235929600 238551040 755302400 760872960 ⟨⟨225219683661, 225219683670⟩, ⟨216642085326, 233956694368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 238551040 239861760 749731840 755302400 ⟨⟨221054441424, 221054441430⟩, ⟨216207988058, 225953584202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 241172480 749731840 755302400 ⟨⟨219306499652, 219306499661⟩, ⟨214481228938, 224184355008⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 755302400 760872960 ⟨⟨222576033563, 222576033568⟩, ⟨217715670459, 227489064102⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 241172480 755302400 760872960 ⟨⟨220817808406, 220817808415⟩, ⟨215978639991, 225709543129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 235929600 238551040 760872960 766443520 ⟨⟨226755774378, 226755774388⟩, ⟨218151623023, 235519335881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235929600 238551040 766443520 772014080 ⟨⟨228290993257, 228290993265⟩, ⟨219660288326, 237081101929⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 238551040 239861760 760872960 766443520 ⟨⟨224096765605, 224096765611⟩, ⟨219222494756, 229023680713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 239861760 241172480 760872960 766443520 ⟨⟨222328275042, 222328275051⟩, ⟨217475210542, 227233886333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 238551040 241172480 766443520 772014080 ⟨⟨224726870916, 224726870923⟩, ⟨216158569440, 233454363222⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 230686720 241172480 749731840 772014080 t = true :=
  ⟨_, (join_su (m := 235929600) (by decide) (join_sr (m := 760872960) (by decide) (join_su (m := 233308160) (by decide) (join_sr (m := 755302400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 755302400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 233308160) (by decide) (join_sr (m := 766443520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 766443520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 760872960) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 755302400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 755302400) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 239861760) (by decide) (leaf_ok cell12) (leaf_ok cell13)))) (join_su (m := 238551040) (by decide) (join_sr (m := 766443520) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_sr (m := 766443520) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell16) (leaf_ok cell17)) (leaf_ok cell18)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (143/160 : ℝ) (589/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((230686720 : ℤ) : ℝ) / (D : ℝ)) = (11/40 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((749731840 : ℤ) : ℝ) / (D : ℝ)) = (143/160 : ℝ) := by norm_num [D]
  have e3 : (((772014080 : ℤ) : ℝ) / (D : ℝ)) = (589/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
