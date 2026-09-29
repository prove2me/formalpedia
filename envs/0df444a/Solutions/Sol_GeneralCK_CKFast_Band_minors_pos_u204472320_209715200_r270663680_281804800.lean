-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r270663680_281804800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:33:52.31738+00:00
-- url     : https://prove2.me/submissions/2d9df044-041a-4c36-956b-b9050f2ba700

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [413/1280, 43/128]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 270663680 273448960 ⟨⟨105545792275, 105545792281⟩, ⟨102049620456, 109084331235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 204472320 205783040 273448960 276234240 ⟨⟨106557953785, 106557953791⟩, ⟨103054246277, 110104042763⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 205783040 207093760 270663680 273448960 ⟨⟨104690222946, 104690222951⟩, ⟨101210492857, 108212040170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 273448960 276234240 ⟨⟨105695190827, 105695190828⟩, ⟨102207948558, 109224535827⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 205783040 276234240 279019520 ⟨⟨107568976844, 107568976852⟩, ⟨104057743334, 111122605850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 204472320 205783040 279019520 281804800 ⟨⟨108578867911, 108578867918⟩, ⟨105060118022, 112140027011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205783040 207093760 276234240 279019520 ⟨⟨106699044713, 106699044718⟩, ⟨103204299602, 110235907856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 205783040 207093760 279019520 281804800 ⟨⟨107701790889, 107701790894⟩, ⟨104199552213, 111246162596⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 208404480 270663680 273448960 ⟨⟨103839546508, 103839546514⟩, ⟨100376097668, 107344805906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207093760 208404480 273448960 276234240 ⟨⟨104837339670, 104837339677⟩, ⟨101366402462, 108350104271⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 208404480 209715200 270663680 273448960 ⟨⟨102993693305, 102993693311⟩, ⟨99546367604, 106482556354⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 208404480 209715200 273448960 276234240 ⟨⟨103984330560, 103984330566⟩, ⟨100529540590, 107480675918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 207093760 208404480 276234240 279019520 ⟨⟨105834042872, 105834042878⟩, ⟨102355626288, 109354303390⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 207093760 208404480 279019520 281804800 ⟨⟨106829662221, 106829662227⟩, ⟨103343775195, 110357409423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209715200 276234240 279019520 ⟨⟨104973901465, 104973901472⟩, ⟨101511655881, 108477720189⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 208404480 209715200 279019520 281804800 ⟨⟨105962411958, 105962411965⟩, ⟨102492719359, 109473695155⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 270663680 281804800 t = true :=
  ⟨_, (join_su (m := 207093760) (by decide) (join_sr (m := 276234240) (by decide) (join_su (m := 205783040) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 273448960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 205783040) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 279019520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 276234240) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 273448960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 273448960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 208404480) (by decide) (join_sr (m := 279019520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 279019520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (413/1280 : ℝ) (43/128 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  have e3 : (((281804800 : ℤ) : ℝ) / (D : ℝ)) = (43/128 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
