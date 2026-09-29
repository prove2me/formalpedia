-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u241172480_242483200_r153681920_159252480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T10:57:30.66164+00:00
-- url     : https://prove2.me/submissions/fb83216d-bf91-44d3-94fe-e83759047def

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/80, 37/128]`, `ρ ∈ [469/2560, 243/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 241172480 241500160 153681920 155074560 ⟨⟨48274404493, 48274404500⟩, ⟨47449875489, 49101954790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 241500160 241827840 153681920 155074560 ⟨⟨48163063301, 48163063303⟩, ⟨47339557228, 48989584683⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 241172480 241500160 155074560 156467200 ⟨⟨48698627831, 48698627836⟩, ⟨47873161577, 49527116741⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 241500160 241827840 155074560 156467200 ⟨⟨48586356846, 48586356848⟩, ⟨47761914947, 49413815428⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 241827840 242155520 153681920 155074560 ⟨⟨48051872267, 48051872273⟩, ⟨47229386861, 48877367025⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 242155520 242483200 153681920 155074560 ⟨⟨47940830838, 47940830843⟩, ⟨47119363841, 48765301245⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 241827840 242155520 155074560 156467200 ⟨⟨48474236964, 48474236970⟩, ⟨47650817150, 49300667508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 242155520 242483200 155074560 156467200 ⟨⟨48362267625, 48362267630⟩, ⟨47539867637, 49187672407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 241172480 241500160 156467200 157859840 ⟨⟨49122666996, 49122667001⟩, ⟨48296263805, 49952094207⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 241500160 241827840 156467200 157859840 ⟨⟨49009467413, 49009467415⟩, ⟨48184089990, 49837862884⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 241172480 241500160 157859840 159252480 ⟨⟨49546522419, 49546522424⟩, ⟨48719182600, 50376887618⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 241500160 241827840 157859840 159252480 ⟨⟨49432395424, 49432395427⟩, ⟨48606082786, 50261727479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 241827840 242155520 156467200 157859840 ⟨⟨48896419866, 48896419873⟩, ⟨48072065945, 49723785893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 242155520 242483200 156467200 157859840 ⟨⟨48783523797, 48783523803⟩, ⟨47960191116, 49609862654⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 241827840 242155520 157859840 159252480 ⟨⟨49318421398, 49318421403⟩, ⟨48493133668, 50146722604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 242155520 242483200 157859840 159252480 ⟨⟨49204599774, 49204599779⟩, ⟨48380334694, 50031872407⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 241172480 242483200 153681920 159252480 t = true :=
  ⟨_, (join_sr (m := 156467200) (by decide) (join_su (m := 241827840) (by decide) (join_sr (m := 155074560) (by decide) (join_su (m := 241500160) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 241500160) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 155074560) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 242155520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 241827840) (by decide) (join_sr (m := 157859840) (by decide) (join_su (m := 241500160) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 241500160) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 157859840) (by decide) (join_su (m := 242155520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 242155520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/80 : ℝ) (37/128 : ℝ) →
    rho ∈ Set.Icc (469/2560 : ℝ) (243/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((241172480 : ℤ) : ℝ) / (D : ℝ)) = (23/80 : ℝ) := by norm_num [D]
  have e1 : (((242483200 : ℤ) : ℝ) / (D : ℝ)) = (37/128 : ℝ) := by norm_num [D]
  have e2 : (((153681920 : ℤ) : ℝ) / (D : ℝ)) = (469/2560 : ℝ) := by norm_num [D]
  have e3 : (((159252480 : ℤ) : ℝ) / (D : ℝ)) = (243/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
