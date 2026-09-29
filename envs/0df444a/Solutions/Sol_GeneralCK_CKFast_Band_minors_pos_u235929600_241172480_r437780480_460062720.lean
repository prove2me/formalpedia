-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r437780480_460062720
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:16:52.673555+00:00
-- url     : https://prove2.me/submissions/402ee58b-e290-48c6-bf77-3691de5ea890

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [167/320, 351/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 437780480 443351040 ⟨⟨136250641638, 136250641646⟩, ⟨132151293190, 140402715111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 237240320 238551040 437780480 443351040 ⟨⟨135111060618, 135111060625⟩, ⟨131031719517, 139242842092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 235929600 237240320 443351040 448921600 ⟨⟨137870536274, 137870536281⟩, ⟨133756830933, 142036998916⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 443351040 448921600 ⟨⟨136719026613, 136719026620⟩, ⟨132625369034, 140865159610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 238551040 239861760 437780480 443351040 ⟨⟨133975490714, 133975490719⟩, ⟨129916023498, 138087115684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 239861760 241172480 437780480 443351040 ⟨⟨132843882590, 132843882596⟩, ⟨128804157281, 136935485055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 238551040 239861760 443351040 448921600 ⟨⟨135571531830, 135571531835⟩, ⟨131497789372, 139697469796⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 239861760 241172480 443351040 448921600 ⟨⟨134428002702, 134428002709⟩, ⟨130374044185, 138533878777⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 235929600 237240320 448921600 454492160 ⟨⟨139488519504, 139488519511⟩, ⟨135360469850, 143669357734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 237240320 238551040 448921600 454492160 ⟨⟨138325124397, 138325124405⟩, ⟨134217162179, 142485596097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 235929600 237240320 454492160 460062720 ⟨⟨141104612292, 141104612300⟩, ⟨136962230711, 145299812715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 237240320 238551040 454492160 460062720 ⟨⟨139929374382, 139929374390⟩, ⟨135807119174, 144104172146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 448921600 454492160 ⟨⟨137165747228, 137165747233⟩, ⟨133077740635, 141305986118⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 239861760 241172480 448921600 454492160 ⟨⟨136010338892, 136010338900⟩, ⟨131942157558, 140130477238⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 238551040 239861760 454492160 460062720 ⟨⟨138758156777, 138758156782⟩, ⟨134655896978, 142912684690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 454492160 460062720 ⟨⟨137590910500, 137590910508⟩, ⟨133508516572, 141725299942⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 437780480 460062720 t = true :=
  ⟨_, (join_sr (m := 448921600) (by decide) (join_su (m := 238551040) (by decide) (join_sr (m := 443351040) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 237240320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 443351040) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 239861760) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 238551040) (by decide) (join_sr (m := 454492160) (by decide) (join_su (m := 237240320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 237240320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 454492160) (by decide) (join_su (m := 239861760) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 239861760) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (167/320 : ℝ) (351/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((437780480 : ℤ) : ℝ) / (D : ℝ)) = (167/320 : ℝ) := by norm_num [D]
  have e3 : (((460062720 : ℤ) : ℝ) / (D : ℝ)) = (351/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
