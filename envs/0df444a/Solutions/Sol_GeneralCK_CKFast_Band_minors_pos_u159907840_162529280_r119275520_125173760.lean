-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u159907840_162529280_r119275520_125173760
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T08:29:42.707957+00:00
-- url     : https://prove2.me/submissions/c793218b-8552-45f8-943e-4d20f1e8f240

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [61/320, 31/160]`, `ρ ∈ [91/640, 191/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 159907840 160563200 119275520 120750080 ⟨⟨65049846530, 65049846536⟩, ⟨63172124379, 66942216736⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 160563200 120750080 122224640 ⟨⟨65804465250, 65804465258⟩, ⟨63924097866, 67699476462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 160563200 161218560 119275520 120750080 ⟨⟨64766830557, 64766830563⟩, ⟨62894898360, 66653331256⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 160563200 161218560 120750080 122224640 ⟨⟨65518502570, 65518502576⟩, ⟨63643932237, 67407637382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 159907840 160563200 122224640 123699200 ⟨⟨66558121397, 66558121404⟩, ⟨64675115062, 68455767281⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 159907840 160563200 123699200 125173760 ⟨⟨67310818853, 67310818861⟩, ⟨65425179825, 69211093111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 160563200 161218560 122224640 123699200 ⟨⟨66269222879, 66269222886⟩, ⟨64392020601, 68160985566⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 160563200 161218560 123699200 125173760 ⟨⟨67018995310, 67018995316⟩, ⟨65139167246, 68913379669⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 161218560 161873920 119275520 120750080 ⟨⟨64485238151, 64485238157⟩, ⟨62619055033, 66365910974⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 161218560 161873920 120750080 122224640 ⟨⟨65233974520, 65233974528⟩, ⟨63365160366, 67117274559⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 161873920 162529280 119275520 120750080 ⟨⟨64205055459, 64205055460⟩, ⟨62344580977, 66079941587⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 161873920 162529280 120750080 122224640 ⟨⟨64950867170, 64950867173⟩, ⟨63087768752, 66828373613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 161218560 161873920 122224640 123699200 ⟨⟨65981769939, 65981769945⟩, ⟨64110330844, 67867691050⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 161218560 161873920 123699200 125173760 ⟨⟨66728628168, 66728628175⟩, ⟨64854570200, 68617164240⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 161873920 162529280 122224640 123699200 ⟨⟨65695748562, 65695748565⟩, ⟨63830032211, 67575869269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 161873920 162529280 123699200 125173760 ⟨⟨66439703337, 66439703340⟩, ⟨64571375027, 68322432290⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 159907840 162529280 119275520 125173760 t = true :=
  ⟨_, (join_su (m := 161218560) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 160563200) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 120750080) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 160563200) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 123699200) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 122224640) (by decide) (join_su (m := 161873920) (by decide) (join_sr (m := 120750080) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 120750080) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 161873920) (by decide) (join_sr (m := 123699200) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 123699200) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (61/320 : ℝ) (31/160 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (191/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((159907840 : ℤ) : ℝ) / (D : ℝ)) = (61/320 : ℝ) := by norm_num [D]
  have e1 : (((162529280 : ℤ) : ℝ) / (D : ℝ)) = (31/160 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((125173760 : ℤ) : ℝ) / (D : ℝ)) = (191/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
