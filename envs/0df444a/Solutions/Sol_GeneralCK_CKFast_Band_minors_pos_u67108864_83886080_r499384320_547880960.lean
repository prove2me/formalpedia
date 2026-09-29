-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u67108864_83886080_r499384320_547880960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:58:09.901398+00:00
-- url     : https://prove2.me/submissions/8b955d5b-3449-4df0-8d92-9d8ec5e138d2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [2/25, 1/10]`, `ρ ∈ [381/640, 209/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 67108864 71303168 499384320 511508480 ⟨⟨379463051375, 379463051390⟩, ⟨355427383328, 404232576062⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 67108864 71303168 511508480 523632640 ⟨⟨385610656745, 385610656759⟩, ⟨361590897399, 410338882847⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 71303168 75497472 499384320 511508480 ⟨⟨371175224000, 371175224013⟩, ⟨347644840138, 395435024540⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 71303168 75497472 511508480 523632640 ⟨⟨377292186613, 377292186627⟩, ⟨353766971104, 401522990552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 67108864 71303168 523632640 535756800 ⟨⟨391703963189, 391703963203⟩, ⟨367700164862, 416391390517⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 67108864 71303168 535756800 547880960 ⟨⟨397745467296, 397745467310⟩, ⟨373757622571, 422392628077⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 71303168 75497472 523632640 535756800 ⟨⟨383356219336, 383356219350⟩, ⟨359836443386, 407558234597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 71303168 75497472 535756800 547880960 ⟨⟨389369709816, 389369709830⟩, ⟨365855579536, 413543186399⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 75497472 79691776 499384320 511508480 ⟨⟨363128782328, 363128782339⟩, ⟨340083666342, 386898059052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 75497472 79691776 511508480 523632640 ⟨⟨369210738582, 369210738595⟩, ⟨346160915533, 392962375850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 79691776 83886080 499384320 511508480 ⟨⟨355308626560, 355308626572⟩, ⟨332730183761, 378605310732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 79691776 83886080 511508480 523632640 ⟨⟨361351604942, 361351604956⟩, ⟨338759374966, 384641135160⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 75497472 79691776 523632640 535756800 ⟨⟨375241198364, 375241198378⟩, ⟨352187122649, 398975155247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 75497472 79691776 535756800 547880960 ⟨⟨381222441310, 381222441323⟩, ⟨358164498605, 404938726277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 79691776 83886080 523632640 535756800 ⟨⟨367344569094, 367344569108⟩, ⟨344739158211, 390626693577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 79691776 83886080 535756800 547880960 ⟨⟨373289692230, 373289692244⟩, ⟨350671635802, 396564213964⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 67108864 83886080 499384320 547880960 t = true :=
  ⟨_, (join_su (m := 75497472) (by decide) (join_sr (m := 523632640) (by decide) (join_su (m := 71303168) (by decide) (join_sr (m := 511508480) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 511508480) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 71303168) (by decide) (join_sr (m := 535756800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 535756800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 523632640) (by decide) (join_su (m := 79691776) (by decide) (join_sr (m := 511508480) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 511508480) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 79691776) (by decide) (join_sr (m := 535756800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 535756800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (2/25 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (381/640 : ℝ) (209/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e1 : (((83886080 : ℤ) : ℝ) / (D : ℝ)) = (1/10 : ℝ) := by norm_num [D]
  have e2 : (((499384320 : ℤ) : ℝ) / (D : ℝ)) = (381/640 : ℝ) := by norm_num [D]
  have e3 : (((547880960 : ℤ) : ℝ) / (D : ℝ)) = (209/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
