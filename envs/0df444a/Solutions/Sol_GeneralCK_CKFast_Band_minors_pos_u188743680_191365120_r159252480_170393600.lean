-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_191365120_r159252480_170393600
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T02:41:02.931596+00:00
-- url     : https://prove2.me/submissions/dc7a9fba-cd88-490c-a484-d14eca59c9f7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 73/320]`, `ρ ∈ [243/1280, 13/64]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 189399040 159252480 162037760 ⟨⟨71057103936, 71057103942⟩, ⟨69003139609, 73128236248⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 189399040 190054400 159252480 162037760 ⟨⟨70758311844, 70758311850⟩, ⟨68710455732, 72823252528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 188743680 189399040 162037760 164823040 ⟨⟨72226084191, 72226084197⟩, ⟨70167439500, 74301892262⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 189399040 190054400 162037760 164823040 ⟨⟨71922851106, 71922851112⟩, ⟨69870326605, 73992455910⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 190054400 190709760 159252480 162037760 ⟨⟨70460666064, 70460666070⟩, ⟨68418883761, 72519450175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 190709760 191365120 159252480 162037760 ⟨⟨70164157088, 70164157094⟩, ⟨68128414493, 72216819370⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 190054400 190709760 162037760 164823040 ⟨⟨71620776085, 71620776091⟩, ⟨69574337379, 73684212663⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 190709760 191365120 162037760 164823040 ⟨⟨71319849551, 71319849557⟩, ⟨69279462550, 73377152630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 188743680 189399040 164823040 167608320 ⟨⟨73393176333, 73393176339⟩, ⟨71329864257, 75473647052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 189399040 190054400 164823040 167608320 ⟨⟨73085523366, 73085523373⟩, ⟨71028343251, 75159779391⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 188743680 189399040 167608320 170393600 ⟨⟨74558392049, 74558392055⟩, ⟨72490425475, 76643512405⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 189399040 190054400 167608320 170393600 ⟨⟨74246340138, 74246340144⟩, ⟨72184517088, 76325234575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 190054400 190709760 164823040 167608320 ⟨⟨72779040004, 72779040012⟩, ⟨70727957467, 74847116354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 190709760 191365120 164823040 167608320 ⟨⟨72473716603, 72473716609⟩, ⟨70428697565, 74535647987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 190054400 190709760 167608320 170393600 ⟨⟨73935469163, 73935469169⟩, ⟨71879755271, 76008172679⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 190709760 191365120 167608320 170393600 ⟨⟨73625769413, 73625769419⟩, ⟨71576130616, 75692316699⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 191365120 159252480 170393600 t = true :=
  ⟨_, (join_sr (m := 164823040) (by decide) (join_su (m := 190054400) (by decide) (join_sr (m := 162037760) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 189399040) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 162037760) (by decide) (join_su (m := 190709760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 190709760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 190054400) (by decide) (join_sr (m := 167608320) (by decide) (join_su (m := 189399040) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 189399040) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 167608320) (by decide) (join_su (m := 190709760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 190709760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (73/320 : ℝ) →
    rho ∈ Set.Icc (243/1280 : ℝ) (13/64 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((191365120 : ℤ) : ℝ) / (D : ℝ)) = (73/320 : ℝ) := by norm_num [D]
  have e2 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  have e3 : (((170393600 : ℤ) : ℝ) / (D : ℝ)) = (13/64 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
