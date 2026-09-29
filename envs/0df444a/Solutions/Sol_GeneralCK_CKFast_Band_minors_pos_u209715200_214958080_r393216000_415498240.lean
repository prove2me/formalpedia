-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_214958080_r393216000_415498240
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:19:59.682007+00:00
-- url     : https://prove2.me/submissions/a013ded5-bf3b-4129-af1f-4bd888576b2a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 41/160]`, `ρ ∈ [15/32, 317/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 211025920 393216000 398786560 ⟨⟨144984063714, 144984063721⟩, ⟨140574876255, 149452383458⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 211025920 212336640 393216000 398786560 ⟨⟨143850885102, 143850885110⟩, ⟨139464528597, 148296010596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 211025920 398786560 404357120 ⟨⟨146867867579, 146867867587⟩, ⟨142443464171, 151351375874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 211025920 212336640 398786560 404357120 ⟨⟨145722214989, 145722214997⟩, ⟨141320670277, 150182505462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 212336640 213647360 393216000 398786560 ⟨⟨142722811313, 142722811316⟩, ⟨138359107701, 147144923790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 213647360 214958080 393216000 398786560 ⟨⟨141599776988, 141599776996⟩, ⟨137258550453, 145999055413⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 213647360 398786560 404357120 ⟨⟨144581674993, 144581674997⟩, ⟨140202812122, 149018927580⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 213647360 214958080 398786560 404357120 ⟨⟨143446182402, 143446182410⟩, ⟨139089826729, 147860574803⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 211025920 404357120 409927680 ⟨⟨148748446435, 148748446442⟩, ⟨144308860862, 153247108147⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 211025920 212336640 404357120 409927680 ⟨⟨147590385928, 147590385935⟩, ⟨143173685654, 152065807403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 209715200 211025920 409927680 415498240 ⟨⟨150625837643, 150625837651⟩, ⟨146171103232, 155139618099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 211025920 212336640 409927680 415498240 ⟨⟨149455434340, 149455434348⟩, ⟨145023610712, 153945953280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 212336640 213647360 404357120 409927680 ⟨⟨146437444774, 146437444776⟩, ⟨142043454166, 150889804633⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 213647360 214958080 404357120 409927680 ⟨⟨145289557963, 145289557970⟩, ⟨140918103569, 149719032624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 212336640 213647360 409927680 415498240 ⟨⟨148290156159, 148290156163⟩, ⟨143881068915, 152757590876⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 213647360 214958080 409927680 415498240 ⟨⟨147129938279, 147129938286⟩, ⟨142743415173, 151574463891⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 214958080 393216000 415498240 t = true :=
  ⟨_, (join_sr (m := 404357120) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 398786560) (by decide) (join_su (m := 211025920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 211025920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 398786560) (by decide) (join_su (m := 213647360) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 213647360) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 212336640) (by decide) (join_sr (m := 409927680) (by decide) (join_su (m := 211025920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 211025920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 409927680) (by decide) (join_su (m := 213647360) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 213647360) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (41/160 : ℝ) →
    rho ∈ Set.Icc (15/32 : ℝ) (317/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e2 : (((393216000 : ℤ) : ℝ) / (D : ℝ)) = (15/32 : ℝ) := by norm_num [D]
  have e3 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
