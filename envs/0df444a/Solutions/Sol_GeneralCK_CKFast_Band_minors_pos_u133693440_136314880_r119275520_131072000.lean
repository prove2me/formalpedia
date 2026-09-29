-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u133693440_136314880_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:08:01.58084+00:00
-- url     : https://prove2.me/submissions/60f695fc-580e-4571-8cd9-a7f98adb253f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [51/320, 13/80]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 133693440 134348800 119275520 122224640 ⟨⟨78163735879, 78163735887⟩, ⟨75452612629, 80904627624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 134348800 135004160 119275520 122224640 ⟨⟨77808232211, 77808232220⟩, ⟨75107959588, 80538065822⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 133693440 134348800 122224640 125173760 ⟨⟨79925859427, 79925859434⟩, ⟨77208134777, 82673279701⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 134348800 135004160 122224640 125173760 ⟨⟨79563462289, 79563462296⟩, ⟨76856602108, 82299812161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 135004160 135659520 119275520 122224640 ⟨⟨77454899838, 77454899845⟩, ⟨74765390495, 80173764946⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 135659520 136314880 119275520 122224640 ⟨⟨77103714596, 77103714600⟩, ⟨74424882284, 79811699707⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 135004160 135659520 122224640 125173760 ⟨⟨79203265846, 79203265853⟩, ⟨76507182954, 81928634756⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 135659520 136314880 122224640 125173760 ⟨⟨78845245721, 78845245723⟩, ⟨76159854022, 81559721987⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 133693440 134348800 125173760 128122880 ⟨⟨81681960203, 81681960210⟩, ⟨78957693578, 84435849415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 134348800 135004160 125173760 128122880 ⟨⟨81312737804, 81312737813⟩, ⟨78599348655, 84055545180⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133693440 134348800 128122880 131072000 ⟨⟨83432097153, 83432097162⟩, ⟨80701347117, 86192396574⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 134348800 135004160 128122880 131072000 ⟨⟨83056116734, 83056116743⟩, ⟨80336256366, 85805323696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 135004160 135659520 125173760 128122880 ⟨⟨80945744700, 80945744707⟩, ⟨78243146021, 83677559474⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 135659520 136314880 125173760 128122880 ⟨⟨80580956304, 80580956308⟩, ⟨77889062167, 83301866601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 135004160 135659520 128122880 131072000 ⟨⟨82682393422, 82682393429⟩, ⟨79973335899, 85420596949⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 135659520 136314880 128122880 131072000 ⟨⟨82310902437, 82310902442⟩, ⟨79612562008, 85038190445⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 133693440 136314880 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 135004160) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 134348800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 134348800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 135659520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 135659520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 135004160) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 134348800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 134348800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 135659520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 135659520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (51/320 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((133693440 : ℤ) : ℝ) / (D : ℝ)) = (51/320 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
