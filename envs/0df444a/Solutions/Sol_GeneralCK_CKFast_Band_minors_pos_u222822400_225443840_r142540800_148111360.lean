-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_225443840_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:49:50.417404+00:00
-- url     : https://prove2.me/submissions/94d9f687-9c34-4882-8954-bc960e2222f6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 43/160]`, `ρ ∈ [87/512, 113/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 222822400 223477760 142540800 143933440 ⟨⟨50878540913, 50878540918⟩, ⟨49401729462, 52364651107⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 222822400 223477760 143933440 145326080 ⟨⟨51358050325, 51358050331⟩, ⟨49879366711, 52846037687⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 223477760 224133120 142540800 143933440 ⟨⟨50653367052, 50653367057⟩, ⟨49179798802, 52136199896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223477760 224133120 143933440 145326080 ⟨⟨51130877887, 51130877892⟩, ⟨49655442585, 52615582825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 222822400 223477760 145326080 146718720 ⟨⟨51837293224, 51837293229⟩, ⟨50356738329, 53327156856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 222822400 223477760 146718720 148111360 ⟨⟨52316270289, 52316270294⟩, ⟨50833844995, 53808009295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 223477760 224133120 145326080 146718720 ⟨⟨51608125466, 51608125472⟩, ⟨50130823974, 53094701623⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 223477760 224133120 146718720 148111360 ⟨⟨52085110461, 52085110466⟩, ⟨50605943639, 53573556963⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 224133120 224788480 142540800 143933440 ⟨⟨50428894536, 50428894539⟩, ⟨48958552723, 51908467029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224133120 224788480 143933440 145326080 ⟨⟨50904411524, 50904411527⟩, ⟨49432207762, 52385851047⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224788480 225443840 142540800 143933440 ⟨⟨50205117949, 50205117956⟩, ⟨48737985945, 51681446962⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 224788480 225443840 143933440 145326080 ⟨⟨50678645789, 50678645796⟩, ⟨49209656928, 52156836779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224133120 224788480 145326080 146718720 ⟨⟨51379668482, 51379668484⟩, ⟨49905603610, 52862974182⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 224788480 146718720 148111360 ⟨⟨51854666069, 51854666071⟩, ⟨50378740925, 53339837094⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224788480 225443840 145326080 146718720 ⟨⟨51151916792, 51151916798⟩, ⟨49681071892, 52631968925⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224788480 225443840 146718720 148111360 ⟨⟨51624931605, 51624931611⟩, ⟨50152231481, 53106844053⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 225443840 142540800 148111360 t = true :=
  ⟨_, (join_su (m := 224133120) (by decide) (join_sr (m := 145326080) (by decide) (join_su (m := 223477760) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 143933440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 223477760) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 146718720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 145326080) (by decide) (join_su (m := 224788480) (by decide) (join_sr (m := 143933440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 143933440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 224788480) (by decide) (join_sr (m := 146718720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 146718720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
