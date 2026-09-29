-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u162529280_165150720_r119275520_125173760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:30:46.462771+00:00
-- url     : https://prove2.me/submissions/6d684f8d-e8b5-4df2-9ec8-c5920386bb06

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [31/160, 63/320]`, `ρ ∈ [91/640, 191/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 162529280 163184640 119275520 120750080 ⟨⟨63926268795, 63926268801⟩, ⟨62071462949, 65795408973⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 162529280 163184640 120750080 122224640 ⟨⟨64669166753, 64669166760⟩, ⟨62811744069, 66540920342⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 163184640 163840000 119275520 120750080 ⟨⟨63648864661, 63648864667⟩, ⟨61799687865, 65512299194⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 163184640 163840000 120750080 122224640 ⟨⟨64388859690, 64388859698⟩, ⟨62537073154, 66254900727⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 163184640 122224640 123699200 ⟨⟨65411144906, 65411144912⟩, ⟨63551111296, 67285505946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 163184640 123699200 125173760 ⟨⟨66152206895, 66152206903⟩, ⟨64289568243, 68029169462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 163184640 163840000 122224640 123699200 ⟨⟨65127945312, 65127945318⟩, ⟨63273554858, 66996586984⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 163184640 163840000 123699200 125173760 ⟨⟨65866125110, 65866125116⟩, ⟨64009136533, 67737361583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 163840000 164495360 119275520 120750080 ⟨⟨63372829719, 63372829726⟩, ⟨61529242809, 65230598485⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 163840000 164495360 120750080 122224640 ⟨⟨64109932565, 64109932572⟩, ⟨62263743012, 65970300927⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 164495360 165150720 119275520 120750080 ⟨⟨63098150802, 63098150808⟩, ⟨61260115030, 64950293258⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 164495360 165150720 120750080 122224640 ⟨⟨63832372131, 63832372137⟩, ⟨61991740810, 65687107274⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 163840000 164495360 122224640 123699200 ⟨⟨64846136284, 64846136292⟩, ⟨62997349822, 66709098465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 163840000 164495360 123699200 125173760 ⟨⟨65581444408, 65581444416⟩, ⟨63730066741, 67446994657⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 164495360 165150720 122224640 123699200 ⟨⟨64565704504, 64565704512⟩, ⟨62722483280, 66423026644⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 164495360 165150720 123699200 125173760 ⟨⟨65298151394, 65298151401⟩, ⟨63452345884, 67158054869⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 162529280 165150720 119275520 125173760 t = true :=
  ⟨_, (join_su (m := 163840000) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 163184640) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 120750080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 163184640) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 123699200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 122224640) (by decide) (join_su (m := 164495360) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 120750080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 164495360) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 123699200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (31/160 : ℝ) (63/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (191/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e1 : (((165150720 : ℤ) : ℝ) / (D : ℝ)) = (63/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
