-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_162529280_r125173760_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:29:47.984199+00:00
-- url     : https://prove2.me/submissions/2a1d263b-4234-49bd-984a-a46db4a399d4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 31/160]`, `ρ ∈ [191/1280, 5/32]` by 15 cells of the computing
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
theorem cell0 : cellOK 159907840 160563200 125173760 126648320 ⟨⟨68062561487, 68062561494⟩, ⟨66174295983, 69965457849⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 160563200 126648320 128122880 ⟨⟨68813353144, 68813353150⟩, ⟨66922467354, 70718865375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 160563200 161218560 125173760 126648320 ⟨⟨67767823666, 67767823672⟩, ⟨65885375942, 69664823520⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160563200 161218560 126648320 128122880 ⟨⟨68515711732, 68515711738⟩, ⟨66630650445, 70415320941⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159907840 160563200 128122880 131072000 ⟨⟨69937765913, 69937765919⟩, ⟨67584080863, 72314331930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 160563200 161218560 128122880 129597440 ⟨⟨69262663275, 69262663283⟩, ⟨67374994490, 71164875730⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 160563200 161218560 129597440 131072000 ⟨⟨70008682045, 70008682053⟩, ⟨68118411798, 71913491664⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 161218560 161873920 125173760 126648320 ⟨⟨67474552952, 67474552959⟩, ⟨65597882145, 69365697906⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 161218560 161873920 126648320 128122880 ⟨⟨68219548018, 68219548024⟩, ⟨66340270374, 70113295800⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 161873920 162529280 125173760 126648320 ⟨⟨67182735179, 67182735183⟩, ⟨65311800853, 69068066389⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161873920 162529280 126648320 128122880 ⟨⟨67924847757, 67924847759⟩, ⟨66051313329, 69812775264⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161218560 161873920 128122880 129597440 ⟨⟨68963617070, 68963617078⟩, ⟨67081738565, 70859961665⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 161873920 129597440 131072000 ⟨⟨69706763801, 69706763807⟩, ⟨67822290378, 71605699219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161873920 162529280 128122880 129597440 ⟨⟨68666044717, 68666044720⟩, ⟨66789916070, 70556562593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161873920 162529280 129597440 131072000 ⟨⟨69406329691, 69406329694⟩, ⟨67527612680, 71299432037⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 162529280 125173760 131072000 t = true :=
  ⟨_, (join_su (m := 161218560) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 160563200) (by decide) (join_sr (m := 126648320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126648320) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 160563200) (by decide) (leaf_ok cell4) (join_sr (m := 129597440) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 128122880) (by decide) (join_su (m := 161873920) (by decide) (join_sr (m := 126648320) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 126648320) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 161873920) (by decide) (join_sr (m := 129597440) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 129597440) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (191/1280 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
