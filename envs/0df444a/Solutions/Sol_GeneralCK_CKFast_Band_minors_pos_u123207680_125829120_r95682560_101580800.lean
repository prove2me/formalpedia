-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u123207680_125829120_r95682560_101580800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:19:03.313525+00:00
-- url     : https://prove2.me/submissions/3e75756c-f4af-4051-a05d-79dbb45ccfe6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/320, 3/20]`, `ρ ∈ [73/640, 31/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 123207680 123863040 95682560 97157120 ⟨⟨68399916958, 68399916967⟩, ⟨66165758621, 70655159594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 123207680 123863040 97157120 98631680 ⟨⟨69370590971, 69370590978⟩, ⟨67133180006, 71629062608⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 123863040 124518400 95682560 97157120 ⟨⟨68070404581, 68070404590⟩, ⟨65845174513, 70316565441⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 123863040 124518400 97157120 98631680 ⟨⟨69037001931, 69037001938⟩, ⟨66808527862, 71286383758⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 123207680 123863040 98631680 100106240 ⟨⟨70339276010, 70339276017⟩, ⟨68098628592, 72600960414⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 123207680 123863040 100106240 101580800 ⟨⟨71305983033, 71305983040⟩, ⟨69062115202, 73570864099⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 123863040 124518400 98631680 100106240 ⟨⟨70001634090, 70001634097⟩, ⟨67769931949, 72254220893⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 123863040 124518400 100106240 101580800 ⟨⟨70964311824, 70964311832⟩, ⟨68729397413, 73220087740⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 124518400 125173760 95682560 97157120 ⟨⟨67743190449, 67743190458⟩, ⟨65526807208, 69980352861⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 124518400 125173760 97157120 98631680 ⟨⟨68705732460, 68705732468⟩, ⟨66486113887, 70946107751⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 125173760 125829120 95682560 97157120 ⟨⟨67418246210, 67418246217⟩, ⟨65210629475, 69646492346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 125173760 125829120 97157120 98631680 ⟨⟨68376754014, 68376754021⟩, ⟨66165910662, 70608204883⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 124518400 125173760 98631680 100106240 ⟨⟨69666332754, 69666332761⟩, ⟨67443494540, 71909905170⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 124518400 125173760 100106240 101580800 ⟨⟨70625001907, 70625001916⟩, ⟨68398959616, 72871755820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 125173760 125829120 98631680 100106240 ⟨⟨69333343271, 69333343278⟩, ⟨67119288752, 71567983359⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 125173760 125829120 100106240 101580800 ⟨⟨70288024371, 70288024379⟩, ⟨68070774019, 72525838280⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 123207680 125829120 95682560 101580800 t = true :=
  ⟨_, (join_su (m := 124518400) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 123863040) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 97157120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 123863040) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 100106240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 98631680) (by decide) (join_su (m := 125173760) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 97157120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 125173760) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 100106240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/320 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (31/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((123207680 : ℤ) : ℝ) / (D : ℝ)) = (47/320 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
