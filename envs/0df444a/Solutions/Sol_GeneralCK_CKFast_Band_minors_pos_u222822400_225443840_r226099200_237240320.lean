-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u222822400_225443840_r226099200_237240320
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:20:52.155989+00:00
-- url     : https://prove2.me/submissions/4fa60868-b26e-48f8-8476-ee05f58ffba8

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/64, 43/160]`, `ρ ∈ [69/256, 181/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 222822400 223477760 226099200 228884480 ⟨⟨79432249379, 79432249386⟩, ⟨77560144139, 81318074269⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 223477760 224133120 226099200 228884480 ⟨⟨79091669484, 79091669491⟩, ⟨77224475938, 80972529386⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 222822400 223477760 228884480 231669760 ⟨⟨80361130592, 80361130598⟩, ⟨78485078770, 82250907750⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 223477760 224133120 228884480 231669760 ⟨⟨80016914474, 80016914481⟩, ⟨78145783640, 81901717519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 224133120 224788480 226099200 228884480 ⟨⟨78752021489, 78752021492⟩, ⟨76889717351, 80627939016⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 224788480 225443840 226099200 228884480 ⟨⟨78413298679, 78413298684⟩, ⟨76555861831, 80284296277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 224133120 224788480 228884480 231669760 ⟨⟨79673636123, 79673636126⟩, ⟨77807404007, 81553487648⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 224788480 225443840 228884480 231669760 ⟨⟨79331288795, 79331288802⟩, ⟨77469933291, 81206211235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 223477760 231669760 234455040 ⟨⟨81289101581, 81289101587⟩, ⟨79409107503, 83182826606⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 223477760 224133120 231669760 234455040 ⟨⟨80941259897, 80941259903⟩, ⟨79066196012, 82830001775⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 222822400 223477760 234455040 237240320 ⟨⟨82216167045, 82216167052⟩, ⟨80332235014, 84113835560⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 223477760 224133120 234455040 237240320 ⟨⟨81864710384, 81864710390⟩, ⟨79985717657, 83757386810⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 224133120 224788480 231669760 234455040 ⟨⟨80594361747, 80594361749⟩, ⟨78724205796, 82478143054⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224788480 225443840 231669760 234455040 ⟨⟨80248400358, 80248400364⟩, ⟨78383130251, 82127243513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224133120 224788480 234455040 237240320 ⟨⟨81514202922, 81514202925⟩, ⟨79640127256, 83401909818⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 224788480 225443840 234455040 237240320 ⟨⟨81164637861, 81164637868⟩, ⟨79295457181, 83047397629⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 222822400 225443840 226099200 237240320 t = true :=
  ⟨_, (join_sr (m := 231669760) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 228884480) (by decide) (join_su (m := 223477760) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 223477760) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 228884480) (by decide) (join_su (m := 224788480) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 224788480) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 224133120) (by decide) (join_sr (m := 234455040) (by decide) (join_su (m := 223477760) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 223477760) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 234455040) (by decide) (join_su (m := 224788480) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 224788480) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/64 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (69/256 : ℝ) (181/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((222822400 : ℤ) : ℝ) / (D : ℝ)) = (17/64 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  have e3 : (((237240320 : ℤ) : ℝ) / (D : ℝ)) = (181/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
