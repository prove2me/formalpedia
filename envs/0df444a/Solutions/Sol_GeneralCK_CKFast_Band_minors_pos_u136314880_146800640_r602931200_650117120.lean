-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_146800640_r602931200_650117120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:53:30.807724+00:00
-- url     : https://prove2.me/submissions/d7c0a6a6-72b5-4c1b-a374-46b999b0c170

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 7/40]`, `ρ ∈ [23/32, 31/40]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 138936320 602931200 614727680 ⟨⟨311648912313, 311648912319⟩, ⟨298477186424, 325098596354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 138936320 141557760 602931200 614727680 ⟨⟨307761554507, 307761554519⟩, ⟨294722403775, 321077480176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 138936320 614727680 626524160 ⟨⟨316564061009, 316564061015⟩, ⟨303347370865, 330054350558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 138936320 141557760 614727680 626524160 ⟨⟨312640405833, 312640405843⟩, ⟨299555036814, 325998377965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 141557760 144179200 602931200 614727680 ⟨⟨303910959797, 303910959808⟩, ⟨291002618280, 317094851118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 144179200 146800640 602931200 614727680 ⟨⟨300096199286, 300096199297⟩, ⟨287316941141, 313149743093⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 141557760 144179200 614727680 626524160 ⟨⟨308753033134, 308753033145⟩, ⟨295797286735, 321980339419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 144179200 146800640 614727680 626524160 ⟨⟨304901032959, 304901032970⟩, ⟨292073248465, 317999290190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 138936320 626524160 638320640 ⟨⟨321458337182, 321458337185⟩, ⟨308197119644, 334988792098⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 138936320 141557760 626524160 638320640 ⟨⟨317498913748, 317498913759⟩, ⟨304367760402, 330898492330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 138936320 638320640 650117120 ⟨⟨326332500154, 326332500160⟩, ⟨313027170190, 339902701398⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 138936320 141557760 638320640 650117120 ⟨⟨322337812502, 322337812514⟩, ⟨309161287536, 335778578064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 141557760 144179200 626524160 638320640 ⟨⟨313575286869, 313575286880⟩, ⟨300572565571, 326845569533⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 144179200 146800640 626524160 638320640 ⟨⟨309686565205, 309686565216⟩, ⟨296810679385, 322829099899⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 141557760 144179200 638320640 650117120 ⟨⟨318378430769, 318378430780⟩, ⟨305329143955, 331691271194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 144179200 146800640 638320640 650117120 ⟨⟨314453481895, 314453481907⟩, ⟨301529899830, 327639877471⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 146800640 602931200 650117120 t = true :=
  ⟨_, (join_sr (m := 626524160) (by decide) (join_su (m := 141557760) (by decide) (join_sr (m := 614727680) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 138936320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 614727680) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 144179200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 141557760) (by decide) (join_sr (m := 638320640) (by decide) (join_su (m := 138936320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 138936320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 638320640) (by decide) (join_su (m := 144179200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 144179200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (23/32 : ℝ) (31/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((602931200 : ℤ) : ℝ) / (D : ℝ)) = (23/32 : ℝ) := by norm_num [D]
  have e3 : (((650117120 : ℤ) : ℝ) / (D : ℝ)) = (31/40 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
