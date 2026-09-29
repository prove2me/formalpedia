-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u102236160_104857600_r95682560_107479040
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:38:45.202436+00:00
-- url     : https://prove2.me/submissions/5c8d0d6b-b5df-4962-85bd-53e1d15e83ca

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/320, 1/8]`, `ρ ∈ [73/640, 41/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 102236160 102891520 95682560 98631680 ⟨⟨80913549017, 80913549025⟩, ⟨77611363590, 84260661403⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 102891520 103546880 95682560 98631680 ⟨⟨80489650756, 80489650760⟩, ⟨77204258734, 83819559661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 102236160 102891520 98631680 101580800 ⟨⟨83134945214, 83134945224⟩, ⟨79824845379, 86489767897⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 102891520 103546880 98631680 101580800 ⟨⟨82701374762, 82701374768⟩, ⟨79408076586, 86038990136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 103546880 104202240 95682560 98631680 ⟨⟨80069294866, 80069294874⟩, ⟨76800519044, 83382183411⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104202240 104857600 95682560 98631680 ⟨⟨79652430711, 79652430721⟩, ⟨76400096746, 82948479021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 103546880 104202240 98631680 101580800 ⟨⟨82271402822, 82271402830⟩, ⟨78994729714, 85591993287⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 104202240 104857600 98631680 101580800 ⟨⟨81844978248, 81844978255⟩, ⟨78584756456, 85148723242⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 102236160 102891520 101580800 104529920 ⟨⟨85344669750, 85344669759⟩, ⟨82026792883, 88707065710⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 102891520 103546880 101580800 104529920 ⟨⟨84901572302, 84901572308⟩, ⟨81600503298, 88246759143⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 102236160 102891520 104529920 107479040 ⟨⟨87542877389, 87542877399⟩, ⟨84217357921, 90912712574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 102891520 103546880 104529920 107479040 ⟨⟨87090395252, 87090395256⟩, ⟨83781687865, 90443021464⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 103546880 104202240 101580800 104529920 ⟨⟨84462127455, 84462127465⟩, ⟨81177690368, 87790286836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 104202240 104857600 101580800 104529920 ⟨⟨84026283597, 84026283605⟩, ⟨80758305296, 87337594235⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 103546880 104202240 104529920 107479040 ⟨⟨86641617821, 86641617831⟩, ⟨83349547243, 89977215945⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 104202240 104857600 104529920 107479040 ⟨⟨86196493046, 86196493054⟩, ⟨82920886798, 89515241055⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 102236160 104857600 95682560 107479040 t = true :=
  ⟨_, (join_sr (m := 101580800) (by decide) (join_su (m := 103546880) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 102891520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 102891520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 98631680) (by decide) (join_su (m := 104202240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 104202240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 103546880) (by decide) (join_sr (m := 104529920) (by decide) (join_su (m := 102891520) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 102891520) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 104529920) (by decide) (join_su (m := 104202240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 104202240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/320 : ℝ) (1/8 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (41/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((102236160 : ℤ) : ℝ) / (D : ℝ)) = (39/320 : ℝ) := by norm_num [D]
  have e1 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
