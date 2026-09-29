-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_249036800_r237240320_248381440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:58:52.048157+00:00
-- url     : https://prove2.me/submissions/f77e561a-db1b-4254-86bf-eada5bd6ada6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 19/64]`, `ρ ∈ [181/640, 379/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247070720 237240320 240025600 ⟨⟨70915968068, 70915968075⟩, ⟨69193310782, 72650656515⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247070720 247726080 237240320 240025600 ⟨⟨70591341467, 70591341471⟩, ⟨68872924281, 72321747181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 246415360 247070720 240025600 242810880 ⟨⟨71715126349, 71715126356⟩, ⟨69988868669, 73453425399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247070720 247726080 240025600 242810880 ⟨⟨71387087597, 71387087601⟩, ⟨69665079285, 73121094745⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247726080 248381440 237240320 240025600 ⟨⟨70267454780, 70267454787⟩, ⟨68553260442, 71993595257⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 248381440 249036800 237240320 240025600 ⟨⟨69944302831, 69944302838⟩, ⟨68234314200, 71666195449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 248381440 240025600 242810880 ⟨⟨71059793378, 71059793384⟩, ⟨69342017185, 72789526118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248381440 249036800 240025600 242810880 ⟨⟨70733238495, 70733238501⟩, ⟨69019677282, 72458714199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 246415360 247070720 242810880 245596160 ⟨⟨72513710686, 72513710692⟩, ⟨70783854186, 74255618716⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 247070720 247726080 242810880 245596160 ⟨⟨72182267109, 72182267113⟩, ⟨70456669189, 73919874129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 246415360 247070720 245596160 248381440 ⟨⟨73311723757, 73311723762⟩, ⟨71578270002, 75057239153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 247070720 247726080 245596160 248381440 ⟨⟨72976882640, 72976882642⟩, ⟨71247696617, 74718087975⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 247726080 248381440 242810880 245596160 ⟨⟨71851572613, 71851572618⟩, ⟨70130216023, 73584896109⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248381440 249036800 242810880 245596160 ⟨⟨71521621975, 71521621982⟩, ⟨69804489582, 73250679318⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 247726080 248381440 245596160 248381440 ⟨⟨72642795078, 72642795083⟩, ⟨70917859543, 74379707834⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248381440 249036800 245596160 248381440 ⟨⟨72309455829, 72309455835⟩, ⟨70588753649, 74042093369⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 249036800 237240320 248381440 t = true :=
  ⟨_, (join_sr (m := 242810880) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 240025600) (by decide) (join_su (m := 247070720) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 247070720) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 240025600) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 248381440) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 247726080) (by decide) (join_sr (m := 245596160) (by decide) (join_su (m := 247070720) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 247070720) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 245596160) (by decide) (join_su (m := 248381440) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 248381440) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (181/640 : ℝ) (379/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  have e3 : (((248381440 : ℤ) : ℝ) / (D : ℝ)) = (379/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
