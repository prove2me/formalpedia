-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u41943040_46137344_r135659520_159907840
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:45:44.227138+00:00
-- url     : https://prove2.me/submissions/01a7d74b-b5ef-465a-8584-611f9010455a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/20, 11/200]`, `ρ ∈ [207/1280, 61/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 41943040 42991616 135659520 141721600 ⟨⟨191940187064, 191940187082⟩, ⟨180617089479, 203643232173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 42991616 44040192 135659520 141721600 ⟨⟨189644600935, 189644600949⟩, ⟨178489002950, 201171140233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 41943040 42991616 141721600 147783680 ⟨⟨197891388315, 197891388329⟩, ⟨186601653692, 209549794562⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 42991616 44040192 141721600 147783680 ⟨⟨195565908187, 195565908205⟩, ⟨184440512585, 207051459732⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 44040192 45088768 135659520 141721600 ⟨⟨187402449068, 187402449086⟩, ⟨176409429516, 198757729052⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 45088768 46137344 135659520 141721600 ⟨⟨185211696938, 185211696956⟩, ⟨174376550260, 196400732897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 44040192 45088768 141721600 147783680 ⟨⟨193293493332, 193293493349⟩, ⟨182327695813, 204611230497⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 45088768 46137344 141721600 147783680 ⟨⟨191072156048, 191072156061⟩, ⟨180261419918, 202226900965⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 41943040 42991616 147783680 153845760 ⟨⟨203722113019, 203722113033⟩, ⟨192467043221, 215335005226⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 42991616 44040192 147783680 153845760 ⟨⟨201369059446, 201369059460⟩, ⟨190275214679, 212812673115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 41943040 42991616 153845760 159907840 ⟨⟨209438065596, 209438065610⟩, ⟨198218773540, 221004737496⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 42991616 44040192 153845760 159907840 ⟨⟨207059574914, 207059574929⟩, ⟨195998444309, 218460467551⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 44040192 45088768 147783680 153845760 ⟨⟨199068662236, 199068662253⟩, ⟨188131474751, 210347840630⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 45088768 46137344 147783680 153845760 ⟨⟨196818980163, 196818980179⟩, ⟨186034075771, 207938360508⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 44040192 45088768 153845760 159907840 ⟨⟨204733298125, 204733298139⟩, ⟨193825927519, 215973066465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 45088768 46137344 153845760 159907840 ⟨⟨202457339916, 202457339930⟩, ⟨191699511388, 213540444258⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 41943040 46137344 135659520 159907840 t = true :=
  ⟨_, (join_sr (m := 147783680) (by decide) (join_su (m := 44040192) (by decide) (join_sr (m := 141721600) (by decide) (join_su (m := 42991616) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 42991616) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 141721600) (by decide) (join_su (m := 45088768) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 45088768) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 44040192) (by decide) (join_sr (m := 153845760) (by decide) (join_su (m := 42991616) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 42991616) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 153845760) (by decide) (join_su (m := 45088768) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 45088768) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/20 : ℝ) (11/200 : ℝ) →
    rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((41943040 : ℤ) : ℝ) / (D : ℝ)) = (1/20 : ℝ) := by norm_num [D]
  have e1 : (((46137344 : ℤ) : ℝ) / (D : ℝ)) = (11/200 : ℝ) := by norm_num [D]
  have e2 : (((135659520 : ℤ) : ℝ) / (D : ℝ)) = (207/1280 : ℝ) := by norm_num [D]
  have e3 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
