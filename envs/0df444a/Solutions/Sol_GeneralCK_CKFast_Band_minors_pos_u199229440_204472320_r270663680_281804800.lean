-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_204472320_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:34:16.025159+00:00
-- url     : https://prove2.me/submissions/b71c689e-8cbb-4a1d-af05-e12f966154d2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 39/160]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 200540160 270663680 273448960 ⟨⟨109018433808, 109018433812⟩, ⟨105454840990, 112625549201⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 200540160 273448960 276234240 ⟨⟨110059560971, 110059560973⟩, ⟨106488341660, 113674311758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 200540160 201850880 270663680 273448960 ⟨⟨108142572170, 108142572176⟩, ⟨104596087759, 111732284867⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 200540160 201850880 273448960 276234240 ⟨⟨109176429057, 109176429063⟩, ⟨105622340345, 112773756369⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 200540160 276234240 279019520 ⟨⟨111099447429, 111099447433⟩, ⟨107520612783, 114721822130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 200540160 279019520 281804800 ⟨⟨112138100398, 112138100402⟩, ⟨108551661502, 115768087602⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 200540160 201850880 276234240 279019520 ⟨⟨110209071479, 110209071487⟩, ⟨106647389243, 113814002310⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 200540160 201850880 279019520 281804800 ⟨⟨111240506456, 111240506464⟩, ⟨107671241407, 114853029771⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 201850880 203161600 270663680 273448960 ⟨⟨107271894205, 107271894213⟩, ⟨103742347723, 110844378347⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 201850880 203161600 273448960 276234240 ⟨⟨108298500123, 108298500129⟩, ⟨104761371878, 111878577714⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 203161600 204472320 270663680 273448960 ⟨⟨106406325341, 106406325348⟩, ⟨102893548881, 109961752431⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 203161600 204472320 273448960 276234240 ⟨⟨107425699498, 107425699504⟩, ⟨103905364150, 110988698500⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 201850880 203161600 276234240 279019520 ⟨⟨109323917359, 109323917367⟩, ⟨105779217758, 112911577678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 201850880 203161600 279019520 281804800 ⟨⟨110348152741, 110348152748⟩, ⟨106795892126, 113943385130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203161600 204472320 276234240 279019520 ⟨⟨108443910310, 108443910317⟩, ⟨104916026117, 112014470873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203161600 204472320 279019520 281804800 ⟨⟨109460964417, 109460964423⟩, ⟨105925541360, 113039076247⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 204472320 270663680 281804800 t = true :=
  ⟨_, (join_su (m := 201850880) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 200540160) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 273448960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 200540160) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 279019520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 276234240) (by decide) (join_su (m := 203161600) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 273448960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 203161600) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 279019520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
