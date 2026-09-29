-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u235929600_241172480_r337510400_348651520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:38:11.103774+00:00
-- url     : https://prove2.me/submissions/3a5ae138-ec84-48ee-9543-b654e6c42bfb

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/32, 23/80]`, `ρ ∈ [103/256, 133/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 235929600 237240320 337510400 340295680 ⟨⟨106326091779, 106326091785⟩, ⟨103019580815, 109669933970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 235929600 237240320 340295680 343080960 ⟨⟨107155695707, 107155695713⟩, ⟨103842343192, 110506412090⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 237240320 238551040 337510400 340295680 ⟨⟨105412486357, 105412486364⟩, ⟨102119759716, 108742350424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 237240320 238551040 340295680 343080960 ⟨⟨106235673093, 106235673099⟩, ⟨102936128346, 109572388681⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 235929600 237240320 343080960 345866240 ⟨⟨107984716938, 107984716944⟩, ⟨104664525429, 111342304760⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235929600 237240320 345866240 348651520 ⟨⟨108813158443, 108813158449⟩, ⟨105486130482, 112177614973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 237240320 238551040 343080960 345866240 ⟨⟨107058290787, 107058290794⟩, ⟨103751930306, 110401855339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 237240320 238551040 345866240 348651520 ⟨⟨107880342330, 107880342337⟩, ⟨104567168472, 111230753301⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 238551040 239861760 337510400 340295680 ⟨⟨104502684250, 104502684254⟩, ⟨101223631577, 107818682455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 238551040 239861760 340295680 343080960 ⟨⟨105319463394, 105319463399⟩, ⟨102033616277, 108642290218⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 239861760 241172480 337510400 340295680 ⟨⟨103596635645, 103596635652⟩, ⟨100331147973, 106898878844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 239861760 241172480 340295680 343080960 ⟨⟨104407016765, 104407016771⟩, ⟨101134758519, 107716065452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 238551040 239861760 343080960 345866240 ⟨⟨106135686915, 106135686917⟩, ⟨102843047540, 109465339984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 238551040 239861760 345866240 348651520 ⟨⟨106951357615, 106951357619⟩, ⟨103651928160, 110287834574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 239861760 241172480 343080960 345866240 ⟨⟨105216855435, 105216855443⟩, ⟨101937828627, 108532707422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 239861760 241172480 345866240 348651520 ⟨⟨106026154386, 106026154393⟩, ⟨102740361009, 109348807495⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 235929600 241172480 337510400 348651520 t = true :=
  ⟨_, (join_su (m := 238551040) (by decide) (join_sr (m := 343080960) (by decide) (join_su (m := 237240320) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 340295680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 237240320) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 345866240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 343080960) (by decide) (join_su (m := 239861760) (by decide) (join_sr (m := 340295680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 340295680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 239861760) (by decide) (join_sr (m := 345866240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 345866240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/32 : ℝ) (23/80 : ℝ) →
    rho ∈ Set.Icc (103/256 : ℝ) (133/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e1 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e2 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  have e3 : (((348651520 : ℤ) : ℝ) / (D : ℝ)) = (133/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
