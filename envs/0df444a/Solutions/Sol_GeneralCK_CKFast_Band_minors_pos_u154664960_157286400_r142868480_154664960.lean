-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u154664960_157286400_r142868480_154664960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:39:22.858976+00:00
-- url     : https://prove2.me/submissions/4c0fe76b-ee62-4ed0-ae43-6ef2df213c68

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [59/320, 3/16]`, `ρ ∈ [109/640, 59/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 154664960 155320320 142868480 145817600 ⟨⟨80081749743, 80081749749⟩, ⟨77631560712, 82555771315⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 155320320 155975680 142868480 145817600 ⟨⟨79738171968, 79738171971⟩, ⟨77296621094, 82203413880⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 154664960 155320320 145817600 148766720 ⟨⟨81604284575, 81604284582⟩, ⟨79148281158, 84084084490⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 155320320 155975680 145817600 148766720 ⟨⟨81255016197, 81255016200⟩, ⟨78807663551, 83726024718⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 155975680 156631040 142868480 145817600 ⟨⟨79396312597, 79396312604⟩, ⟨76963340523, 81852835543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 156631040 157286400 142868480 145817600 ⟨⟨79056155037, 79056155043⟩, ⟨76631703033, 81504019055⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 155975680 156631040 145817600 148766720 ⟨⟨80907485462, 80907485470⟩, ⟨78468724314, 83369763184⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 156631040 157286400 145817600 148766720 ⟨⟨80561675656, 80561675664⟩, ⟨78131447362, 83015282518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 154664960 155320320 148766720 151715840 ⟨⟨83122899553, 83122899560⟩, ⟨80661115939, 85608443432⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 155320320 155975680 148766720 151715840 ⟨⟨82767983482, 82767983486⟩, ⟨80314862775, 85244724712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 154664960 155320320 151715840 154664960 ⟨⟨84637626909, 84637626915⟩, ⟨82170096902, 87128880764⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 155320320 155975680 151715840 154664960 ⟨⟨84277105559, 84277105561⟩, ⟨81818250122, 86759545980⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 155975680 156631040 148766720 151715840 ⟨⟨82414823836, 82414823844⟩, ⟨79970306854, 84882822906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 156631040 157286400 148766720 151715840 ⟨⟨82063403785, 82063403792⟩, ⟨79627431970, 84522720530⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 155975680 156631040 151715840 154664960 ⟨⟨83918358964, 83918358971⟩, ⟨81468119014, 86392046328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 156631040 157286400 151715840 154664960 ⟨⟨83561370184, 83561370191⟩, ⟨81119687260, 86026364217⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 154664960 157286400 142868480 154664960 t = true :=
  ⟨_, (join_sr (m := 148766720) (by decide) (join_su (m := 155975680) (by decide) (join_sr (m := 145817600) (by decide) (join_su (m := 155320320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 155320320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 145817600) (by decide) (join_su (m := 156631040) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 156631040) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 155975680) (by decide) (join_sr (m := 151715840) (by decide) (join_su (m := 155320320) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 155320320) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 151715840) (by decide) (join_su (m := 156631040) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 156631040) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (59/320 : ℝ) (3/16 : ℝ) →
    rho ∈ Set.Icc (109/640 : ℝ) (59/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  have e1 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e2 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  have e3 : (((154664960 : ℤ) : ℝ) / (D : ℝ)) = (59/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
