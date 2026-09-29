-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_211025920_r125829120_131399680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:12:33.915477+00:00
-- url     : https://prove2.me/submissions/83adb248-fb74-469f-900a-3461587c6fba

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 161/640]`, `ρ ∈ [3/20, 401/2560]` by 11 cells of the computing
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
theorem cell0 : cellOK 209715200 210042880 125829120 127221760 ⟨⟨49318855602, 49318855608⟩, ⟨48405932825, 50235465981⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 210042880 210370560 125829120 127221760 ⟨⟨49211215376, 49211215383⟩, ⟨48299546394, 50126563421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 209715200 210370560 127221760 128614400 ⟨⟨49789680013, 49789680019⟩, ⟨48266105429, 51323244103⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 210370560 210698240 125829120 127221760 ⟨⟨49103764547, 49103764552⟩, ⟨48193346093, 50017853554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 210698240 211025920 125829120 127221760 ⟨⟨48996502344, 48996502349⟩, ⟨48087331161, 49909335604⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 210370560 210698240 127221760 128614400 ⟨⟨49626820419, 49626820423⟩, ⟨48715305980, 50542006074⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 210698240 211025920 127221760 128614400 ⟨⟨49518485142, 49518485149⟩, ⟨48608219696, 50432413344⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 209715200 210370560 128614400 130007040 ⟨⟨50313997514, 50313997521⟩, ⟨48788430836, 51849557979⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 209715200 210370560 130007040 131399680 ⟨⟨50837965239, 50837965244⟩, ⟨49310407903, 52375520616⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 210370560 211025920 128614400 130007040 ⟨⟨50094801662, 50094801668⟩, ⟨48572788407, 51626768737⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 210370560 211025920 130007040 131399680 ⟨⟨50616628655, 50616628662⟩, ⟨49092630343, 52150585096⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 211025920 125829120 131399680 t = true :=
  ⟨_, (join_sr (m := 128614400) (by decide) (join_su (m := 210370560) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 210042880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 127221760) (by decide) (join_su (m := 210698240) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 210698240) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 210370560) (by decide) (join_sr (m := 130007040) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 130007040) (by decide) (leaf_ok cell9) (leaf_ok cell10))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (161/640 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (401/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((211025920 : ℤ) : ℝ) / (D : ℝ)) = (161/640 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((131399680 : ℤ) : ℝ) / (D : ℝ)) = (401/2560 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
