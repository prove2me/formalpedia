-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u58720256_67108864_r256901120_305397760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:16:10.728109+00:00
-- url     : https://prove2.me/submissions/71646572-6e8e-4ba8-9340-f016ef6ddd0e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [7/100, 2/25]`, `ρ ∈ [49/160, 233/640]` by 18 cells of the computing
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
theorem cell0 : cellOK 58720256 60817408 256901120 269025280 ⟨⟨257131972309, 257131972321⟩, ⟨239470219840, 275483508912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 60817408 62914560 256901120 269025280 ⟨⟨253093475898, 253093475913⟩, ⟨235755091425, 271104749604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 58720256 60817408 269025280 281149440 ⟨⟨265387628758, 265387628773⟩, ⟨247773383216, 283664375078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 60817408 62914560 269025280 281149440 ⟨⟨261304271368, 261304271383⟩, ⟨244005122105, 279250483076⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 62914560 65011712 256901120 262963200 ⟨⟨247095028051, 247095028065⟩, ⟨234307396037, 260260569227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 62914560 65011712 262963200 269025280 ⟨⟨251218367433, 251218367448⟩, ⟨238434911748, 264373173273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 65011712 67108864 256901120 262963200 ⟨⟨243278197788, 243278197802⟩, ⟨230709366148, 256216222713⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 65011712 67108864 262963200 269025280 ⟨⟨247376409848, 247376409863⟩, ⟨234809180586, 260306632184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 62914560 65011712 269025280 281149440 ⟨⟨257326132090, 257326132105⟩, ⟨240331567544, 274952827596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 65011712 67108864 269025280 281149440 ⟨⟨253448411674, 253448411688⟩, ⟨236748457927, 270766052629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 58720256 60817408 281149440 293273600 ⟨⟨273477033990, 273477034006⟩, ⟨255912137535, 291678342154⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 60817408 62914560 281149440 293273600 ⟨⟨269352746814, 269352746826⟩, ⟨252094880014, 287232938717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 58720256 60817408 293273600 305397760 ⟨⟨281409953230, 281409953245⟩, ⟨263895882356, 299535468812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 60817408 62914560 293273600 305397760 ⟨⟨277248283001, 277248283015⟩, ⟨260033383354, 295061796365⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 62914560 65011712 281149440 293273600 ⟨⟨265331889219, 265331889233⟩, ⟨248371079763, 282901367227⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 65011712 67108864 281149440 293273600 ⟨⟨261409828734, 261409828748⟩, ⟨244736603778, 278678481637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 62914560 65011712 293273600 305397760 ⟨⟨273188231417, 273188231432⟩, ⟨256263040324, 290699566600⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 65011712 67108864 293273600 305397760 ⟨⟨269225326042, 269225326057⟩, ⟨252580845264, 286443832840⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 58720256 67108864 256901120 305397760 t = true :=
  ⟨_, (join_sr (m := 281149440) (by decide) (join_su (m := 62914560) (by decide) (join_sr (m := 269025280) (by decide) (join_su (m := 60817408) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 60817408) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 269025280) (by decide) (join_su (m := 65011712) (by decide) (join_sr (m := 262963200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 262963200) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 65011712) (by decide) (leaf_ok cell8) (leaf_ok cell9)))) (join_su (m := 62914560) (by decide) (join_sr (m := 293273600) (by decide) (join_su (m := 60817408) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 60817408) (by decide) (leaf_ok cell12) (leaf_ok cell13))) (join_sr (m := 293273600) (by decide) (join_su (m := 65011712) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_su (m := 65011712) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (7/100 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (49/160 : ℝ) (233/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((58720256 : ℤ) : ℝ) / (D : ℝ)) = (7/100 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  have e3 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
