-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u62914560_67108864_r87162880_99287040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:07:42.881523+00:00
-- url     : https://prove2.me/submissions/86932c09-fa35-4667-9c80-628105e67306

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/40, 2/25]`, `ρ ∈ [133/1280, 303/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 62914560 63963136 87162880 90193920 ⟨⟨106809546666, 106809546676⟩, ⟨100489185023, 113289125791⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 62914560 63963136 90193920 93224960 ⟨⟨109890971087, 109890971097⟩, ⟨103559905176, 116379768526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 63963136 65011712 87162880 90193920 ⟨⟨105624973846, 105624973856⟩, ⟨99380334543, 112025426095⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 63963136 65011712 90193920 93224960 ⟨⟨108681562479, 108681562493⟩, ⟨102425992994, 115091523066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 62914560 63963136 93224960 96256000 ⟨⟨112943333457, 112943333468⟩, ⟨106602084887, 119440841574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 62914560 63963136 96256000 99287040 ⟨⟨115967255852, 115967255866⟩, ⟨109616325855, 122472987419⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 63963136 65011712 93224960 96256000 ⟨⟨111709772861, 111709772875⟩, ⟨105443782035, 118128745814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 63963136 65011712 96256000 99287040 ⟨⟨114710204292, 114710204302⟩, ⟨108434281467, 121137713181⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 65011712 66060288 87162880 90193920 ⟨⟨104464804179, 104464804181⟩, ⟨98293940697, 110788191670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 65011712 66060288 90193920 93224960 ⟨⟨107496834865, 107496834870⟩, ⟨101314834021, 113829998722⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 66060288 67108864 87162880 90193920 ⟨⟨103328221996, 103328222006⟩, ⟨97229262548, 109576526855⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 66060288 67108864 90193920 93224960 ⟨⟨106335970120, 106335970133⟩, ⟨100225683628, 112594298818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 65011712 66060288 93224960 96256000 ⟨⟨110501151557, 110501151562⟩, ⟨104308509690, 116843607297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 65011712 66060288 96256000 99287040 ⟨⟨113478331750, 113478331755⟩, ⟨107275526523, 119829613613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 66060288 67108864 93224960 96256000 ⟨⟨109316649641, 109316649652⟩, ⟨103195520188, 115584529005⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 66060288 67108864 96256000 99287040 ⟨⟨112270817171, 112270817184⟩, ⟨106139310971, 118547791972⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 62914560 67108864 87162880 99287040 t = true :=
  ⟨_, (join_su (m := 65011712) (by decide) (join_sr (m := 93224960) (by decide) (join_su (m := 63963136) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 90193920) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 63963136) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 96256000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 93224960) (by decide) (join_su (m := 66060288) (by decide) (join_sr (m := 90193920) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 90193920) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 66060288) (by decide) (join_sr (m := 96256000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 96256000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/40 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((62914560 : ℤ) : ℝ) / (D : ℝ)) = (3/40 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((87162880 : ℤ) : ℝ) / (D : ℝ)) = (133/1280 : ℝ) := by norm_num [D]
  have e3 : (((99287040 : ℤ) : ℝ) / (D : ℝ)) = (303/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
