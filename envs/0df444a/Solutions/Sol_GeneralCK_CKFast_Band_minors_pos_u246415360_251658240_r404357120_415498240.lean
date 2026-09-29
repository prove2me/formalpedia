-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r404357120_415498240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:12:06.892114+00:00
-- url     : https://prove2.me/submissions/4baeda23-22cc-4a8e-8475-f84ecb723990

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [617/1280, 317/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 404357120 407142400 ⟨⟨117677999048, 117677999055⟩, ⟨114319491663, 121073215470⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247726080 407142400 409927680 ⟨⟨118445647771, 118445647777⟩, ⟨115080517289, 121847521751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 249036800 404357120 407142400 ⟨⟨116644390405, 116644390413⟩, ⟨113299380209, 120025946865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 407142400 409927680 ⟨⟨117405962795, 117405962801⟩, ⟨114054350934, 120794156118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247726080 409927680 412712960 ⟨⟨119212871116, 119212871124⟩, ⟨115841118453, 122621401574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 246415360 247726080 412712960 415498240 ⟨⟨119979671281, 119979671289⟩, ⟨116601297340, 123394857144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 249036800 409927680 412712960 ⟨⟨118167120058, 118167120064⟩, ⟨114808907306, 121561949306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 247726080 249036800 412712960 415498240 ⟨⟨118927864328, 118927864334⟩, ⟨115563051448, 122329328575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 250347520 404357120 407142400 ⟨⟨115614370323, 115614370330⟩, ⟨112282762418, 118982363051⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 249036800 250347520 407142400 409927680 ⟨⟨116369870881, 116369870887⟩, ⟨113031682991, 119744479511⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251658240 404357120 407142400 ⟨⟨114587893550, 114587893558⟩, ⟨111269594121, 117942417681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 250347520 251658240 407142400 409927680 ⟨⟨115337326792, 115337326799⟩, ⟨112012469300, 118698445603⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 409927680 412712960 ⟨⟨117124966382, 117124966389⟩, ⟨113780199144, 120506190118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 249036800 250347520 412712960 415498240 ⟨⟨117879658900, 117879658906⟩, ⟨114528312939, 121267496956⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251658240 409927680 412712960 ⟨⟨116086364868, 116086364876⟩, ⟨112754949816, 119454077704⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 250347520 251658240 412712960 415498240 ⟨⟨116835009794, 116835009801⟩, ⟨113497037675, 120209316006⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 404357120 415498240 t = true :=
  ⟨_, (join_su (m := 249036800) (by decide) (join_sr (m := 409927680) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 407142400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 407142400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247726080) (by decide) (join_sr (m := 412712960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 412712960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 409927680) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 407142400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 407142400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 250347520) (by decide) (join_sr (m := 412712960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 412712960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (617/1280 : ℝ) (317/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((404357120 : ℤ) : ℝ) / (D : ℝ)) = (617/1280 : ℝ) := by norm_num [D]
  have e3 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
