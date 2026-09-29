-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_167772160_r225443840_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:56:28.543494+00:00
-- url     : https://prove2.me/submissions/9b48ba9a-dc7d-4635-a58e-832cf6d94e61

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 1/5]`, `ρ ∈ [43/160, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163840000 225443840 228392960 ⟨⟨115374933755, 115374933762⟩, ⟨111333113957, 119472549308⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162529280 163840000 228392960 231342080 ⟨⟨116741353408, 116741353417⟩, ⟨112690512795, 120847940621⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163840000 165150720 225443840 228392960 ⟨⟨114450579018, 114450579025⟩, ⟨110432267623, 118524193350⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163840000 165150720 228392960 231342080 ⟨⟨115807916017, 115807916024⟩, ⟨111780600639, 119890488414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 163840000 231342080 234291200 ⟨⟨118105017515, 118105017523⟩, ⟨114045188846, 122220543105⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 163840000 234291200 237240320 ⟨⟨119465946770, 119465946779⟩, ⟨115397162501, 123590377762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163840000 165150720 231342080 234291200 ⟨⟨117162552957, 117162552966⟩, ⟨113126265507, 121254050985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163840000 165150720 234291200 237240320 ⟨⟨118514509963, 118514509970⟩, ⟨114469282057, 122614901487⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 165150720 166461440 225443840 228392960 ⟨⟨113533728877, 113533728885⟩, ⟨109538636510, 117583638991⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165150720 166461440 228392960 231342080 ⟨⟨114882018277, 114882018285⟩, ⟨110877939604, 118940871923⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 166461440 167772160 225443840 228392960 ⟨⟨112624257700, 112624257702⟩, ⟨108652100335, 116650755083⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 166461440 167772160 228392960 231342080 ⟨⟨113963534391, 113963534395⟩, ⟨109982409210, 117998959871⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 165150720 166461440 231342080 234291200 ⟨⟨116227662106, 116227662115⟩, ⟨112214628204, 120295427685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 165150720 166461440 234291200 237240320 ⟨⟨117570679932, 117570679941⟩, ⟨113548721595, 121647326132⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 166461440 167772160 231342080 234291200 ⟨⟨115300219018, 115300219022⟩, ⟨111310156275, 119344541817⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 166461440 167772160 234291200 237240320 ⟨⟨116634330604, 116634330608⟩, ⟨112635360288, 120687520220⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 167772160 225443840 237240320 t = true :=
  ⟨_, (join_su (m := 165150720) (by decide) (join_sr (m := 231342080) (by decide) (join_su (m := 163840000) (by decide) (join_sr (m := 228392960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 228392960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 163840000) (by decide) (join_sr (m := 234291200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 234291200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 231342080) (by decide) (join_su (m := 166461440) (by decide) (join_sr (m := 228392960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 228392960) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 166461440) (by decide) (join_sr (m := 234291200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 234291200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (43/160 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
