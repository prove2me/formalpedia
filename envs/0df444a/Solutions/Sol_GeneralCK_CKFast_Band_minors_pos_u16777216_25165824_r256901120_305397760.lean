-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r256901120_305397760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:29:30.437723+00:00
-- url     : https://prove2.me/submissions/c5f32d49-e9de-4fe1-ab2f-e325b39b9104

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/50, 3/100]`, `ρ ∈ [49/160, 233/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 16777216 18874368 256901120 269025280 ⟨⟨373277719862, 373277719885⟩, ⟨345202975348, 402536882970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 18874368 20971520 256901120 269025280 ⟨⟨364980736106, 364980736125⟩, ⟨337726639929, 393388664287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 16777216 18874368 269025280 281149440 ⟨⟨381529214007, 381529214029⟩, ⟨353911755736, 410240753289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 18874368 20971520 269025280 281149440 ⟨⟨373313559520, 373313559541⟩, ⟨346475809938, 401220561573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 20971520 23068672 256901120 269025280 ⟨⟨357085138199, 357085138217⟩, ⟨330599132050, 384694061845⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 23068672 25165824 256901120 269025280 ⟨⟨349553357228, 349553357245⟩, ⟨323789149257, 376409750022⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 20971520 23068672 269025280 281149440 ⟨⟨365484142507, 365484142524⟩, ⟨339377255023, 392634694960⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 23068672 25165824 269025280 281149440 ⟨⟨358005199723, 358005199740⟩, ⟨332586158201, 384442107807⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 16777216 18874368 281149440 293273600 ⟨⟨389560943518, 389560943540⟩, ⟨362379446292, 417754114539⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 18874368 20971520 281149440 293273600 ⟨⟨381425083133, 381425083154⟩, ⟨354985434106, 408856579266⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 16777216 18874368 293273600 305397760 ⟨⟨397391133229, 397391133251⟩, ⟨370625621281, 425092912506⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 18874368 20971520 293273600 305397760 ⟨⟨389333353780, 389333353801⟩, ⟨363274601083, 416312907595⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 20971520 23068672 281149440 293273600 ⟨⟨373661327818, 373661327839⟩, ⟨347918002461, 400375561825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 23068672 25165824 281149440 293273600 ⟨⟨366235550644, 366235550665⟩, ⟨341148473090, 392272063836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 20971520 23068672 293273600 305397760 ⟨⟨381634474845, 381634474866⟩, ⟨356239940024, 407932943371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 23068672 25165824 293273600 305397760 ⟨⟨374261856885, 374261856905⟩, ⟨349494111306, 399915866875⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 16777216 25165824 256901120 305397760 t = true :=
  ⟨_, (join_sr (m := 281149440) (by decide) (join_su (m := 20971520) (by decide) (join_sr (m := 269025280) (by decide) (join_su (m := 18874368) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 18874368) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 269025280) (by decide) (join_su (m := 23068672) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 23068672) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 20971520) (by decide) (join_sr (m := 293273600) (by decide) (join_su (m := 18874368) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 18874368) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 293273600) (by decide) (join_su (m := 23068672) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 23068672) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) →
    rho ∈ Set.Icc (49/160 : ℝ) (233/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((16777216 : ℤ) : ℝ) / (D : ℝ)) = (1/50 : ℝ) := by norm_num [D]
  have e1 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e2 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  have e3 : (((305397760 : ℤ) : ℝ) / (D : ℝ)) = (233/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
