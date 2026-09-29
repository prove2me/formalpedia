-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u107479040_110100480_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:03:54.619255+00:00
-- url     : https://prove2.me/submissions/c5b68747-7d18-4fa7-b90f-a898861f4650

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/320, 21/160]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 107479040 108134400 95682560 98631680 ⟨⟨77618780435, 77618780443⟩, ⟨74446136844, 80833229452⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 108134400 108789760 95682560 98631680 ⟨⟨77221856208, 77221856215⟩, ⟨74064665347, 80420486575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 107479040 108134400 98631680 101580800 ⟨⟨79764342940, 79764342949⟩, ⟨76583866936, 82986452971⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 108134400 108789760 98631680 101580800 ⟨⟨79358181694, 79358181704⟩, ⟨76193170985, 82564464199⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 108789760 109445120 95682560 98631680 ⟨⟨76828095257, 76828095265⟩, ⟨73686201235, 80011067920⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 109445120 110100480 95682560 98631680 ⟨⟨76437454123, 76437454129⟩, ⟨73310703468, 79604927513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 108789760 109445120 98631680 101580800 ⟨⟨78955235936, 78955235944⟩, ⟨75805535078, 82145851330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 109445120 110100480 98631680 101580800 ⟨⟨78555461728, 78555461732⟩, ⟨75420917679, 81730567932⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 107479040 108134400 101580800 104529920 ⟨⟨81899339930, 81899339937⟩, ⟨78711153315, 85128989326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 108134400 108789760 101580800 104529920 ⟨⟨81484071424, 81484071434⟩, ⟨78311360848, 84697886217⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 107479040 108134400 104529920 107479040 ⟨⟨84023904686, 84023904694⟩, ⟨80828126813, 87260974267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 108134400 108789760 104529920 107479040 ⟨⟨83599656236, 83599656246⟩, ⟨80419363389, 86820885873⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 108789760 109445120 101580800 104529920 ⟨⟨81072068825, 81072068835⟩, ⟨77914679325, 84270208872⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 109445120 110100480 101580800 104529920 ⟨⟨80663287758, 80663287762⟩, ⟨77521066750, 83845910439⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 108789760 109445120 104529920 107479040 ⟨⟨83178722378, 83178722386⟩, ⟨80013760093, 86384271346⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 109445120 110100480 104529920 107479040 ⟨⟨82761058318, 82761058324⟩, ⟨79611274500, 85951083437⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 107479040 110100480 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 108789760) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 108134400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 108134400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 109445120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 109445120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 108789760) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 108134400) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 108134400) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 109445120) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 109445120) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/320 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
