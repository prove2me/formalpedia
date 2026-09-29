-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u233308160_235929600_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T13:07:33.795144+00:00
-- url     : https://prove2.me/submissions/751c6913-ce4e-4e4c-a755-1f844e775a07

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [89/320, 9/32]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 233308160 233963520 270663680 273448960 ⟨⟨87945258799, 87945258805⟩, ⟨86088758488, 89814786157⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 233963520 234618880 270663680 273448960 ⟨⟨87563149028, 87563149032⟩, ⟨85711364970, 89427913985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 233308160 233963520 273448960 276234240 ⟨⟨88805062166, 88805062172⟩, ⟨86944810907, 90678347581⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 233963520 234618880 273448960 276234240 ⟨⟨88419546429, 88419546430⟩, ⟨86564019703, 90288061305⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 234618880 235274240 270663680 273448960 ⟨⟨87181946717, 87181946724⟩, ⟨85334859275, 89041969171⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 235274240 235929600 270663680 273448960 ⟨⟨86801645619, 86801645626⟩, ⟨84959235286, 88656945329⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 234618880 235274240 273448960 276234240 ⟨⟨88034942254, 88034942259⟩, ⟨86184120445, 89898706469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 235274240 235929600 273448960 276234240 ⟨⟨87651243382, 87651243388⟩, ⟨85805107000, 89510276672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 233308160 233963520 276234240 279019520 ⟨⟨89664171526, 89664171532⟩, ⟨87800172027, 91541212226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 233963520 234618880 276234240 279019520 ⟨⟨89275258101, 89275258104⟩, ⟨87415991349, 91147520196⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 233308160 233963520 279019520 281804800 ⟨⟨90522590346, 90522590353⟩, ⟨88654845304, 92403383572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 233963520 234618880 279019520 281804800 ⟨⟨90130287463, 90130287466⟩, ⟨88267283310, 92006294088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 234618880 235274240 276234240 279019520 ⟨⟨88887260265, 88887260273⟩, ⟨87032706663, 90754763610⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 235274240 235929600 276234240 279019520 ⟨⟨88500171746, 88500171753⟩, ⟨86650311822, 90362936056⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 234618880 235274240 279019520 281804800 ⟨⟨89738904122, 89738904129⟩, ⟨87880621281, 91610143977⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 235274240 235929600 279019520 281804800 ⟨⟨89348434032, 89348434039⟩, ⟨87494853056, 91214926809⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 233308160 235929600 270663680 281804800 t = true :=
  ⟨_, (join_sr (m := 276234240) (by decide) (join_su (m := 234618880) (by decide) (join_sr (m := 273448960) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 233963520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 273448960) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 235274240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 234618880) (by decide) (join_sr (m := 279019520) (by decide) (join_su (m := 233963520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 233963520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 279019520) (by decide) (join_su (m := 235274240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 235274240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (89/320 : ℝ) (9/32 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((233308160 : ℤ) : ℝ) / (D : ℝ)) = (89/320 : ℝ) := by norm_num [D]
  have e1 : (((235929600 : ℤ) : ℝ) / (D : ℝ)) = (9/32 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
