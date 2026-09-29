-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u249036800_251658240_r203816960_209387520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T12:27:44.61108+00:00
-- url     : https://prove2.me/submissions/edd37823-a8f0-4b26-947f-3ef041cf5744

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/64, 3/10]`, `ρ ∈ [311/1280, 639/2560]` by 16 cells of the computing
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
theorem cell0 : cellOK 249036800 249692160 203816960 205209600 ⟨⟨59953830026, 59953830033⟩, ⟨58521288470, 61394733187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 249036800 249692160 205209600 206602240 ⟨⟨60350113236, 60350113243⟩, ⟨58915903959, 61792689903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 249692160 250347520 203816960 205209600 ⟨⟨59674292967, 59674292973⟩, ⟨58244608638, 61112313764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 249692160 250347520 205209600 206602240 ⟨⟨60068833587, 60068833592⟩, ⟨58637485696, 61508523755⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 249036800 249692160 206602240 207994880 ⟨⟨60746251968, 60746251974⟩, ⟨59310375143, 62190501961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 249036800 249692160 207994880 209387520 ⟨⟨61142246552, 61142246557⟩, ⟨59704702349, 62588169688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 249692160 250347520 206602240 207994880 ⟨⟨60463231618, 60463231623⟩, ⟨59030220324, 61904590990⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249692160 250347520 207994880 209387520 ⟨⟨60857487383, 60857487388⟩, ⟨59422812849, 62300515790⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 250347520 251002880 203816960 205209600 ⟨⟨59395413925, 59395413928⟩, ⟨57968574072, 60830565254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250347520 251002880 205209600 206602240 ⟨⟨59788214682, 59788214685⟩, ⟨58359715424, 61225031252⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 251002880 251658240 203816960 205209600 ⟨⟨59117188187, 59117188193⟩, ⟨57693180154, 60549482862⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 251002880 251658240 205209600 206602240 ⟨⟨59508251795, 59508251801⟩, ⟨58082588509, 60942207582⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 250347520 251002880 206602240 207994880 ⟨⟨60180874720, 60180874722⟩, ⟨58750716206, 61619356374⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251002880 207994880 209387520 ⟨⟨60573394358, 60573394359⟩, ⟨59141576734, 62013540938⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 251002880 251658240 206602240 207994880 ⟨⟨59899176534, 59899176540⟩, ⟨58471858133, 61334793287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 251002880 251658240 207994880 209387520 ⟨⟨60289962718, 60289962723⟩, ⟨58860989339, 61727240291⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 249036800 251658240 203816960 209387520 t = true :=
  ⟨_, (join_su (m := 250347520) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 249692160) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 205209600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 249692160) (by decide) (join_sr (m := 207994880) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 207994880) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 206602240) (by decide) (join_su (m := 251002880) (by decide) (join_sr (m := 205209600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 205209600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 251002880) (by decide) (join_sr (m := 207994880) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 207994880) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/64 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (639/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((209387520 : ℤ) : ℝ) / (D : ℝ)) = (639/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
