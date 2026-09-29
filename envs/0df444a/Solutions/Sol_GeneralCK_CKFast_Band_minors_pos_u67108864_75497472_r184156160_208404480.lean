-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_75497472_r184156160_208404480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:49:12.32965+00:00
-- url     : https://prove2.me/submissions/b8b9fe0c-defa-49cc-a656-ba3c5bfc6760

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 9/100]`, `ρ ∈ [281/1280, 159/640]` by 17 cells of the computing
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
theorem cell0 : cellOK 67108864 69206016 184156160 190218240 ⟨⟨187148985546, 187148985557⟩, ⟨174860049797, 199877927126⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 69206016 190218240 196280320 ⟨⟨191798790499, 191798790513⟩, ⟨179498754610, 204531545651⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 69206016 71303168 184156160 190218240 ⟨⟨183939962606, 183939962617⟩, ⟨171882582559, 196424509915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 69206016 71303168 190218240 196280320 ⟨⟨188546497250, 188546497263⟩, ⟨176475750461, 201037591934⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 69206016 196280320 202342400 ⟨⟨196391748210, 196391748224⟩, ⟨184081811925, 209127250761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 69206016 202342400 208404480 ⟨⟨200929673975, 200929673988⟩, ⟨188610961018, 213666931046⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 69206016 71303168 196280320 202342400 ⟨⟨193098007179, 193098007190⟩, ⟨181015082038, 205594579371⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 69206016 71303168 202342400 208404480 ⟨⟨197596215598, 197596215611⟩, ⟨185502228173, 210097265546⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 71303168 73400320 184156160 190218240 ⟨⟨180824599248, 180824599261⟩, ⟨168989903545, 193074213327⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 71303168 73400320 190218240 196280320 ⟨⟨185387721739, 185387721750⟩, ⟨173537591828, 197646384478⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 73400320 74448896 184156160 190218240 ⟨⟨178546757336, 178546757346⟩, ⟨170657914683, 186616011174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 74448896 75497472 184156160 190218240 ⟨⟨177055114500, 177055114510⟩, ⟨169240971378, 185047008571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 73400320 75497472 190218240 196280320 ⟨⟨182317917200, 182317917213⟩, ⟨170680218466, 194352857063⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 71303168 73400320 196280320 202342400 ⟨⟨189897586433, 189897586446⟩, ⟨178033195960, 202164229279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 71303168 73400320 202342400 208404480 ⟨⟨194355829402, 194355829416⟩, ⟨182478283273, 206629450761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 73400320 75497472 196280320 202342400 ⟨⟨186786000878, 186786000891⟩, ⟨175132138532, 198831215129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 73400320 75497472 202342400 208404480 ⟨⟨191204092706, 191204092717⟩, ⟨179535157565, 203258582205⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 75497472 184156160 208404480 t = true :=
  ⟨_, (join_su (m := 71303168) (by decide) (join_sr (m := 196280320) (by decide) (join_su (m := 69206016) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 190218240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 69206016) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 202342400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 196280320) (by decide) (join_su (m := 73400320) (by decide) (join_sr (m := 190218240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 190218240) (by decide) (join_su (m := 74448896) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (leaf_ok cell12))) (join_su (m := 73400320) (by decide) (join_sr (m := 202342400) (by decide) (leaf_ok cell13) (leaf_ok cell14)) (join_sr (m := 202342400) (by decide) (leaf_ok cell15) (leaf_ok cell16)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (9/100 : ℝ) →
    rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((75497472 : ℤ) : ℝ) / (D : ℝ)) = (9/100 : ℝ) := by norm_num [D]
  have e2 : (((184156160 : ℤ) : ℝ) / (D : ℝ)) = (281/1280 : ℝ) := by norm_num [D]
  have e3 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
