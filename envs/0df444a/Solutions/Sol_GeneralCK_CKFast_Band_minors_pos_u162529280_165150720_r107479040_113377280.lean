-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_165150720_r107479040_113377280
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:30:00.476088+00:00
-- url     : https://prove2.me/submissions/7fdb599e-dd19-45a2-b9ae-6875f534acdf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 63/320]`, `ρ ∈ [41/320, 173/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163184640 107479040 108953600 ⟨⟨57949528970, 57949528976⟩, ⟨56115874303, 59797543735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162529280 163184640 108953600 110428160 ⟨⟨58699918702, 58699918708⟩, ⟨56863598806, 60550595638⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163184640 163840000 107479040 108953600 ⟨⟨57695729652, 57695729660⟩, ⟨55867643919, 59538097368⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163184640 163840000 108953600 110428160 ⟨⟨58443131145, 58443131151⟩, ⟨56612388027, 60288153375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 163184640 110428160 111902720 ⟨⟨59449358828, 59449358835⟩, ⟨57610379860, 61302691734⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 163184640 111902720 113377280 ⟨⟨60197853140, 60197853148⟩, ⟨58356221225, 62053835841⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163184640 163840000 110428160 111902720 ⟨⟨59189593906, 59189593913⟩, ⟨57356199465, 61037264545⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163184640 163840000 111902720 113377280 ⟨⟨59935121666, 59935121674⟩, ⟨58099081933, 61785434637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 163840000 164495360 107479040 108953600 ⟨⟨57443209304, 57443209311⟩, ⟨55620653398, 59279969816⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 164495360 108953600 110428160 ⟨⟨58187634257, 58187634264⟩, ⟨56362428799, 60027041637⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 164495360 165150720 107479040 108953600 ⟨⟨57191955436, 57191955442⟩, ⟨55374890668, 59023148168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 164495360 165150720 108953600 110428160 ⟨⟨57933415460, 57933415468⟩, ⟨56113708964, 59767247423⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163840000 164495360 110428160 111902720 ⟨⟨58931131231, 58931131239⟩, ⟨57103282190, 60773179469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 163840000 164495360 111902720 113377280 ⟨⟨59673703897, 59673703905⟩, ⟨57843217207, 61518387006⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 164495360 165150720 110428160 111902720 ⟨⟨58673958139, 58673958145⟩, ⟨56851615785, 60510423410⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 164495360 165150720 111902720 113377280 ⟨⟨59413587078, 59413587085⟩, ⟨57588614712, 61252679770⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 165150720 107479040 113377280 t = true :=
  ⟨_, (join_su (m := 163840000) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 163184640) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 108953600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 163184640) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 111902720) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 110428160) (by decide) (join_su (m := 164495360) (by decide) (join_sr (m := 108953600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 108953600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 164495360) (by decide) (join_sr (m := 111902720) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 111902720) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (173/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((113377280 : ℤ) : ℝ) / (D : ℝ)) = (173/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
