-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u131072000_133693440_r95682560_101580800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:01:35.312975+00:00
-- url     : https://prove2.me/submissions/6fd967ac-f9fe-4569-bb44-ef9fa4c17979

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [5/32, 51/320]`, `ρ ∈ [73/640, 31/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 131072000 131727360 95682560 97157120 ⟨⟨64591439399, 64591439408⟩, ⟨62459282958, 66742955820⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 131072000 131727360 97157120 98631680 ⟨⟨65514559635, 65514559642⟩, ⟨63379256469, 67669205513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131727360 132382720 95682560 97157120 ⟨⟨64287733087, 64287733096⟩, ⟨62163597612, 66431095705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 131727360 132382720 97157120 98631680 ⟨⟨65207020323, 65207020330⟩, ⟨63079747127, 67353503859⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 131072000 131727360 98631680 100106240 ⟨⟨66435956892, 66435956900⟩, ⟨64297520483, 68593718685⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 131072000 131727360 100106240 101580800 ⟨⟨67355640046, 67355640055⟩, ⟨65214083775, 69516504307⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131727360 132382720 98631680 100106240 ⟨⟨66124604949, 66124604958⟩, ⟨63994207309, 68274196064⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 131727360 132382720 100106240 101580800 ⟨⟨67040495690, 67040495696⟩, ⟨64906986785, 69193181136⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 132382720 133038080 95682560 97157120 ⟨⟨63986013666, 63986013671⟩, ⟨61869829962, 66121293220⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 132382720 133038080 97157120 98631680 ⟨⟨64901487053, 64901487054⟩, ⟨62782174648, 67039878958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133038080 133693440 95682560 97157120 ⟨⟨63686257802, 63686257809⟩, ⟨61577957585, 65813524104⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 133038080 133693440 97157120 98631680 ⟨⟨64597936320, 64597936327⟩, ⟨62486516441, 66728306382⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 132382720 133038080 98631680 100106240 ⟨⟨65815277941, 65815277946⟩, ⟨63692849914, 67956769057⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 132382720 133038080 100106240 101580800 ⟨⟨66727394904, 66727394909⟩, ⟨64601864236, 68871972185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 133038080 133693440 98631680 100106240 ⟨⟨65507952199, 65507952207⟩, ⟨63393425537, 67641413078⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 133038080 133693440 100106240 101580800 ⟨⟨66416313864, 66416313871⟩, ⟨64298693205, 68552852706⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 131072000 133693440 95682560 101580800 t = true :=
  ⟨_, (join_su (m := 132382720) (by decide) (join_sr (m := 98631680) (by decide) (join_su (m := 131727360) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 97157120) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 131727360) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 100106240) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 98631680) (by decide) (join_su (m := 133038080) (by decide) (join_sr (m := 97157120) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 97157120) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 133038080) (by decide) (join_sr (m := 100106240) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 100106240) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (5/32 : ℝ) (51/320 : ℝ) →
    rho ∈ Set.Icc (73/640 : ℝ) (31/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e1 : (((133693440 : ℤ) : ℝ) / (D : ℝ)) = (51/320 : ℝ) := by norm_num [D]
  have e2 : (((95682560 : ℤ) : ℝ) / (D : ℝ)) = (73/640 : ℝ) := by norm_num [D]
  have e3 : (((101580800 : ℤ) : ℝ) / (D : ℝ)) = (31/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
