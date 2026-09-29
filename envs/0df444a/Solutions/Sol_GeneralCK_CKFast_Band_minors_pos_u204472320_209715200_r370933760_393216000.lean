-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r370933760_393216000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:47:00.988986+00:00
-- url     : https://prove2.me/submissions/4683fbbe-d32a-432a-a7a9-e5e3e22ff2f7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [283/640, 15/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 370933760 376504320 ⟨⟨141798235488, 141798235496⟩, ⟨137357550423, 146299704721⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 205783040 207093760 370933760 376504320 ⟨⟨140694701057, 140694701062⟩, ⟨136277479434, 145172312337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 204472320 205783040 376504320 382074880 ⟨⟨143746428646, 143746428654⟩, ⟨139290269903, 148263332132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 376504320 382074880 ⟨⟨142630099565, 142630099567⟩, ⟨138197431880, 147123121988⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 207093760 208404480 370933760 376504320 ⟨⟨139596503366, 139596503374⟩, ⟨135202552644, 144050452981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 208404480 209715200 370933760 376504320 ⟨⟨138503572494, 138503572502⟩, ⟨134132702645, 142934054159⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207093760 208404480 376504320 382074880 ⟨⟨141519118703, 141519118711⟩, ⟨137109750804, 145988454986⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 208404480 209715200 376504320 382074880 ⟨⟨140413416294, 140413416301⟩, ⟨136027159383, 144859258817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 205783040 382074880 387645440 ⟨⟨145690953077, 145690953085⟩, ⟨141219361344, 150223248712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 205783040 207093760 382074880 387645440 ⟨⟨144561903806, 144561903811⟩, ⟨140113829466, 149070296573⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 204472320 205783040 387645440 393216000 ⟨⟨147631851646, 147631851653⟩, ⟨143144867058, 152179497885⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 205783040 207093760 387645440 393216000 ⟨⟨146490155567, 146490155573⟩, ⟨142026713438, 151013878412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 207093760 208404480 382074880 387645440 ⟨⟨143438213087, 143438213095⟩, ⟨139013466148, 147922896518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 208404480 209715200 382074880 387645440 ⟨⟨142319811315, 142319811323⟩, ⟨137918204231, 146780976439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 208404480 387645440 393216000 ⟨⟨145353827246, 145353827253⟩, ⟨140913738886, 149853818821⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 208404480 209715200 387645440 393216000 ⟨⟨144222797250, 144222797258⟩, ⟨139805876385, 148699247217⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 370933760 393216000 t = true :=
  ⟨_, (join_sr (m := 382074880) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 376504320) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 205783040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 376504320) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 208404480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 207093760) (by decide) (join_sr (m := 387645440) (by decide) (join_su (m := 205783040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 205783040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 387645440) (by decide) (join_su (m := 208404480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 208404480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (283/640 : ℝ) (15/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((370933760 : ℤ) : ℝ) / (D : ℝ)) = (283/640 : ℝ) := by norm_num [D]
  have e3 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
