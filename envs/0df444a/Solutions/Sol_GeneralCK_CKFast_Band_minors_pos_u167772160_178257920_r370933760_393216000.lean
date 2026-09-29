-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u167772160_178257920_r370933760_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T01:47:13.429797+00:00
-- url     : https://prove2.me/submissions/fb2ec38c-19b9-4a4c-8d52-1a57ceb9dc7b

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/5, 17/80]`, `ρ ∈ [283/640, 15/32]` by 17 cells of the computing
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
theorem cell0 : cellOK 167772160 170393600 370933760 376504320 ⟨⟨174541387056, 174541387065⟩, ⟨165989117917, 183293781273⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 167772160 170393600 376504320 382074880 ⟨⟨176845041430, 176845041439⟩, ⟨168263506619, 185626286639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 170393600 173015040 370933760 376504320 ⟨⟨171984246201, 171984246210⟩, ⟨163518973218, 180647217524⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 170393600 173015040 376504320 382074880 ⟨⟨174261885699, 174261885709⟩, ⟨165767295839, 182953801030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 167772160 170393600 382074880 387645440 ⟨⟨179142474581, 179142474590⟩, ⟨170531804196, 187952435002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 167772160 170393600 387645440 393216000 ⟨⟨181433770893, 181433770903⟩, ⟨172794092936, 190272312875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 170393600 173015040 382074880 387645440 ⟨⟨176533525724, 176533525732⟩, ⟨168009743235, 185254255110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 170393600 173015040 387645440 393216000 ⟨⟨178799246718, 178799246728⟩, ⟨170246393890, 187548662205⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 173015040 175636480 370933760 376504320 ⟨⟨169457747396, 169457747405⟩, ⟨161077786542, 178033030339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 173015040 175636480 376504320 382074880 ⟨⟨171709384794, 171709384802⟩, ⟨163300071415, 180313687375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 175636480 176947200 370933760 376504320 ⟨⟨167582467071, 167582467080⟩, ⟨162571144253, 172664303543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 176947200 178257920 370933760 376504320 ⟨⟨166341415540, 166341415548⟩, ⟨161358532095, 171394322485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 175636480 178257920 376504320 382074880 ⟨⟨169186688367, 169186688370⟩, ⟨160861031885, 177705045215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 173015040 175636480 382074880 387645440 ⟨⟨173955238332, 173955238341⟩, ⟨165516690940, 182588436347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 173015040 175636480 387645440 393216000 ⟨⟨176195384689, 176195384696⟩, ⟨167727719947, 184857355799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 175636480 178257920 382074880 387645440 ⟨⟨171406766192, 171406766198⟩, ⟨163051849164, 179954083272⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 175636480 178257920 387645440 393216000 ⟨⟨173621342832, 173621342836⟩, ⟨165237276406, 182197503339⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 167772160 178257920 370933760 393216000 t = true :=
  ⟨_, (join_su (m := 173015040) (by decide) (join_sr (m := 382074880) (by decide) (join_su (m := 170393600) (by decide) (join_sr (m := 376504320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 376504320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 170393600) (by decide) (join_sr (m := 387645440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 387645440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 382074880) (by decide) (join_su (m := 175636480) (by decide) (join_sr (m := 376504320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 376504320) (by decide) (join_su (m := 176947200) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 175636480) (by decide) (join_sr (m := 387645440) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 387645440) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/5 : ℝ) (17/80 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e1 : (((178257920 : ℤ) : ℝ) / (D : ℝ)) = (17/80 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
