-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_162529280_r296222720_319815680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:02:21.851803+00:00
-- url     : https://prove2.me/submissions/3b4f29c9-9ec2-496e-a0ad-181f321ce82a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 31/160]`, `ρ ∈ [113/320, 61/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 157286400 158597120 296222720 302120960 ⟨⟨152713655829, 152713655836⟩, ⟨147379826863, 158132724543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 158597120 159907840 296222720 302120960 ⟨⟨151547855915, 151547855922⟩, ⟨146248066981, 156932137002⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 158597120 302120960 308019200 ⟨⟨155383488075, 155383488084⟩, ⟨150031773908, 160820126682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 158597120 159907840 302120960 308019200 ⟨⟨154201872553, 154201872563⟩, ⟨148884175338, 159603758772⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159907840 161218560 296222720 302120960 ⟨⟨150390690111, 150390690117⟩, ⟨145124564151, 155740570598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 161218560 162529280 296222720 302120960 ⟨⟨149242022472, 149242022481⟩, ⟨144009188908, 154557882734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 159907840 161218560 302120960 308019200 ⟨⟨153028917967, 153028917971⟩, ⟨147744864092, 158396435057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 161218560 162529280 302120960 308019200 ⟨⟨151864488805, 151864488812⟩, ⟨146613711028, 157198013499⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 157286400 158597120 308019200 313917440 ⟨⟨158043498244, 158043498254⟩, ⟨152674044594, 163497559479⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 158597120 159907840 308019200 313917440 ⟨⟨156846249332, 156846249341⟩, ⟨151510786435, 162265596483⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 157286400 158597120 313917440 319815680 ⟨⟨160693835008, 160693835015⟩, ⟨155306784668, 166165174553⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 158597120 159907840 313917440 319815680 ⟨⟨159481131167, 159481131176⟩, ⟨154128042362, 164917797906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 159907840 161218560 308019200 313917440 ⟨⟨155657685344, 155657685349⟩, ⟨150355843070, 161042697878⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161218560 162529280 308019200 313917440 ⟨⟨154477671247, 154477671256⟩, ⟨149209085728, 159828722224⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 159907840 161218560 313917440 319815680 ⟨⟨158277133497, 158277133503⟩, ⟨152957639610, 163679503078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161218560 162529280 313917440 319815680 ⟨⟨157081707479, 157081707489⟩, ⟨151795448041, 162450149260⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 162529280 296222720 319815680 t = true :=
  ⟨_, (join_sr (m := 308019200) (by decide) (join_su (m := 159907840) (by decide) (join_sr (m := 302120960) (by decide) (join_su (m := 158597120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 158597120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 302120960) (by decide) (join_su (m := 161218560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 161218560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 159907840) (by decide) (join_sr (m := 313917440) (by decide) (join_su (m := 158597120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 158597120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 313917440) (by decide) (join_su (m := 161218560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 161218560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (113/320 : ℝ) (61/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((296222720 : ℤ) : ℝ) / (D : ℝ)) = (113/320 : ℝ) := by norm_num [D]
  have e3 : (((319815680 : ℤ) : ℝ) / (D : ℝ)) = (61/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
