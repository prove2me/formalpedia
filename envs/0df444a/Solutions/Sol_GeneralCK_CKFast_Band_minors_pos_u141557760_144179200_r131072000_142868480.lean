-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u141557760_144179200_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:28:10.945839+00:00
-- url     : https://prove2.me/submissions/d7bba6a2-bd04-45c8-9cd6-2bd1d8dc07bf

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [27/160, 11/64]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 141557760 142213120 131072000 134021120 ⟨⟨80729698669, 80729698678⟩, ⟨78117844469, 83368750792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 142213120 142868480 131072000 134021120 ⟨⟨80372865253, 80372865257⟩, ⟨77770939295, 83001811985⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 141557760 142213120 134021120 136970240 ⟨⟨82390262411, 82390262418⟩, ⟨79772178846, 85035487351⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 142213120 142868480 134021120 136970240 ⟨⟨82027106736, 82027106740⟩, ⟨79418964076, 84662214875⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 142868480 143523840 131072000 134021120 ⟨⟨80018038951, 80018038960⟩, ⟨77425966333, 82636957029⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 143523840 144179200 131072000 134021120 ⟨⟨79665198750, 79665198757⟩, ⟨77082905443, 82274163997⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 142868480 143523840 134021120 136970240 ⟨⟨81665982422, 81665982430⟩, ⟨79067705901, 84291050339⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 143523840 144179200 134021120 136970240 ⟨⟨81306868292, 81306868299⟩, ⟨78718384012, 83921971660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 141557760 142213120 136970240 139919360 ⟨⟨84045761391, 84045761398⟩, ⟨81421495963, 86697111466⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 142213120 142868480 136970240 139919360 ⟨⟨83676339654, 83676339656⟩, ⟨81062027135, 86317562177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 141557760 142213120 139919360 142868480 ⟨⟨85696241782, 85696241791⟩, ⟨83065841373, 88353669937⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 142213120 142868480 139919360 142868480 ⟨⟨85320609443, 85320609447⟩, ⟨82700173302, 87967899935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 142868480 143523840 136970240 139919360 ⟨⟨83308972894, 83308972901⟩, ⟨80704538663, 85940144275⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 143523840 144179200 136970240 139919360 ⟨⟨82943639777, 82943639784⟩, ⟨80349010076, 85564835526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 142868480 143523840 139919360 142868480 ⟨⟨84947055080, 84947055087⟩, ⟨82336508739, 87584284145⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 143523840 144179200 139919360 142868480 ⟨⟨84575557209, 84575557216⟩, ⟨81974827055, 87202800190⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 141557760 144179200 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 142868480) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 142213120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 142213120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 143523840) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 143523840) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 142868480) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 142213120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 142213120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 143523840) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 143523840) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (27/160 : ℝ) (11/64 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((141557760 : ℤ) : ℝ) / (D : ℝ)) = (27/160 : ℝ) := by norm_num [D]
  have e1 : (((144179200 : ℤ) : ℝ) / (D : ℝ)) = (11/64 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
