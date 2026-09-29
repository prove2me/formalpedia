-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u154664960_157286400_r154664960_166461440
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:40:04.788853+00:00
-- url     : https://prove2.me/submissions/021af33c-95f2-4ee7-aa21-27faa180bee8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [59/320, 3/16]`, `ρ ∈ [59/320, 127/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 154664960 155320320 154664960 157614080 ⟨⟨86148498552, 86148498560⟩, ⟨83675255575, 88645428779⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 155320320 155975680 154664960 157614080 ⟨⟨85782413844, 85782413847⟩, ⟨83317856639, 88270520313⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 154664960 155320320 157614080 160563200 ⟨⟨87655546075, 87655546081⟩, ⟨85176623174, 90158119450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 155320320 155975680 157614080 160563200 ⟨⟨87283939445, 87283939449⟩, ⟨84813713065, 89777679193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 155975680 156631040 154664960 157614080 ⟨⟨85418121780, 85418121787⟩, ⟨82962191367, 87897464752⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 156631040 157286400 154664960 157614080 ⟨⟨85055605316, 85055605323⟩, ⟨82608243333, 87526244402⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 155975680 156631040 157614080 160563200 ⟨⟨86914142914, 86914142923⟩, ⟨84452554182, 89399109173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 156631040 157286400 157614080 160563200 ⟨⟨86546139338, 86546139345⟩, ⟨84093129995, 89022391599⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 154664960 155320320 160563200 163512320 ⟨⟨89158800754, 89158800762⟩, ⟨86674230607, 91666984425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 155320320 155975680 160563200 163512320 ⟨⟨88781713163, 88781713166⟩, ⟨86305849835, 91281053786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 155320320 163512320 166461440 ⟨⟨90658293559, 90658293567⟩, ⟨88168108472, 93172055044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 155320320 155975680 163512320 166461440 ⟨⟨90275765494, 90275765497⟩, ⟨87794297088, 92780674947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 155975680 156631040 160563200 163512320 ⟨⟨88406452699, 88406452706⟩, ⟨85939237431, 90897010281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 156631040 157286400 160563200 163512320 ⟨⟨88033002119, 88033002127⟩, ⟨85574376766, 90514836032⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 155975680 156631040 163512320 166461440 ⟨⟨89895081164, 89895081171⟩, ⟨87422270796, 92391198463⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 156631040 157286400 163512320 166461440 ⟨⟨89516223236, 89516223243⟩, ⟨87052012874, 92003607619⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 154664960 157286400 154664960 166461440 t = true :=
  ⟨_, (join_sr (m := 160563200) (by decide) (join_su (m := 155975680) (by decide) (join_sr (m := 157614080) (by decide) (join_su (m := 155320320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 155320320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 157614080) (by decide) (join_su (m := 156631040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 156631040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 155975680) (by decide) (join_sr (m := 163512320) (by decide) (join_su (m := 155320320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 155320320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 163512320) (by decide) (join_su (m := 156631040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 156631040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (59/320 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e3 : (((166461440 : ℤ) : ℝ) / (D : ℝ)) = (127/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
