-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u136314880_138936320_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:18:59.767621+00:00
-- url     : https://prove2.me/submissions/3e501bee-60e2-4ad6-bc0e-cb51e3c4377e

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [13/80, 53/320]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 136314880 136970240 119275520 122224640 ⟨⟨76754652679, 76754652686⟩, ⟨74086412221, 79451845193⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 136970240 137625600 119275520 122224640 ⟨⟨76407690638, 76407690645⟩, ⟨73749957912, 79094176865⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 136314880 136970240 122224640 125173760 ⟨⟨78489377887, 78489377894⟩, ⟨75814592356, 81193048735⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 136970240 137625600 122224640 125173760 ⟨⟨78135638686, 78135638693⟩, ⟨75471375345, 80828590247⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 137625600 138280960 119275520 122224640 ⟨⟨76062805365, 76062805372⟩, ⟨73415497284, 78738670543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 138280960 138936320 119275520 122224640 ⟨⟨75719974089, 75719974096⟩, ⟨73083008592, 78385302407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 137625600 138280960 122224640 125173760 ⟨⟨77784004794, 77784004800⟩, ⟨75130180697, 80466322144⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 138280960 138936320 122224640 125173760 ⟨⟨77434453230, 77434453237⟩, ⟨74790986449, 80106220396⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 136970240 125173760 128122880 ⟨⟨80218348388, 80218348397⟩, ⟨77537073932, 82928441241⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 136970240 137625600 125173760 128122880 ⟨⟨79857897091, 79857897098⟩, ⟨77187158489, 82557258449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 136314880 136970240 128122880 131072000 ⟨⟨81941619356, 81941619363⟩, ⟨79253911330, 84658078678⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 136970240 137625600 128122880 131072000 ⟨⟨81574520120, 81574520129⟩, ⟨78897360840, 84280236516⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 137625600 138280960 125173760 128122880 ⟨⟨79499578883, 79499578890⟩, ⟨76839293340, 82188293646⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 138280960 138936320 125173760 128122880 ⟨⟨79143370585, 79143370594⟩, ⟨76493456319, 81821522609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 137625600 138280960 128122880 131072000 ⟨⟨81209581015, 81209581022⟩, ⟨78542887845, 83904639191⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 138280960 138936320 128122880 131072000 ⟨⟨80846778666, 80846778675⟩, ⟨78190469977, 83531262303⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 136314880 138936320 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 137625600) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 136970240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 136970240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 138280960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 138280960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 137625600) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 136970240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 136970240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 138280960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 138280960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (13/80 : ℝ) (53/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e1 : (((138936320 : ℤ) : ℝ) / (D : ℝ)) = (53/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
