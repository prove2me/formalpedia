-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r571473920_593756160
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:01:32.017425+00:00
-- url     : https://prove2.me/submissions/13dae672-a663-44ae-a4be-fdab34c232c3

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [109/160, 453/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 571473920 577044480 ⟨⟨215283159946, 215283159955⟩, ⟨206665872199, 224070785176⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 199229440 201850880 577044480 582615040 ⟨⟨217161124686, 217161124695⟩, ⟨208516742101, 225975649432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 204472320 571473920 577044480 ⟨⟨212203013703, 212203013706⟩, ⟨203656311355, 220919101148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 577044480 582615040 ⟨⟨214059678699, 214059678703⟩, ⟨205485848797, 222802726294⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 199229440 201850880 582615040 588185600 ⟨⟨219036599426, 219036599435⟩, ⟨210365161685, 227877978971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 199229440 201850880 588185600 593756160 ⟨⟨220909618611, 220909618621⟩, ⟨212211164740, 229777808896⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 201850880 204472320 582615040 588185600 ⟨⟨215913942998, 215913943002⟩, ⟨207313022673, 224683908658⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 201850880 204472320 588185600 593756160 ⟨⟨217765839588, 217765839592⟩, ⟨209137865346, 226562681841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 204472320 207093760 571473920 577044480 ⟨⟨209144161321, 209144161330⟩, ⟨200667200983, 217789556407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 204472320 207093760 577044480 582615040 ⟨⟨210979451859, 210979451867⟩, ⟨202475342170, 219651855948⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 207093760 209715200 571473920 577044480 ⟨⟨206106118803, 206106118812⟩, ⟨197698074341, 214681649967⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 207093760 209715200 577044480 582615040 ⟨⟨207919963470, 207919963479⟩, ⟨199484758423, 216522541092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 204472320 207093760 582615040 588185600 ⟨⟨212812428891, 212812428901⟩, ⟨204281204462, 221511802503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 204472320 207093760 588185600 593756160 ⟨⟨214643123996, 214643124005⟩, ⟨206084818850, 223369428223⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 207093760 209715200 582615040 588185600 ⟨⟨209731579729, 209731579738⟩, ⟨201269246221, 218361166897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 207093760 209715200 588185600 593756160 ⟨⟨211540997791, 211540997800⟩, ⟨203051567397, 220197558136⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 571473920 593756160 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 582615040) (by decide) (join_su (m := 201850880) (by decide) (join_sr (m := 577044480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 577044480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 201850880) (by decide) (join_sr (m := 588185600) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 588185600) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 582615040) (by decide) (join_su (m := 207093760) (by decide) (join_sr (m := 577044480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 577044480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 207093760) (by decide) (join_sr (m := 588185600) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 588185600) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (109/160 : ℝ) (453/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((571473920 : ℤ) : ℝ) / (D : ℝ)) = (109/160 : ℝ) := by norm_num [D]
  have e3 : (((593756160 : ℤ) : ℝ) / (D : ℝ)) = (453/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
