-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u133693440_136314880_r131072000_142868480
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:26:33.023974+00:00
-- url     : https://prove2.me/submissions/4757fb33-b7f2-46cd-8bcc-dc88448c4822

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [51/320, 13/80]`, `ρ ∈ [5/32, 109/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 133693440 134348800 131072000 134021120 ⟨⟨85176328480, 85176328489⟩, ⟨82439152762, 87942980228⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 134348800 135004160 131072000 134021120 ⟨⟨84793656331, 84793656339⟩, ⟨82067381667, 87549205794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 133693440 134348800 134021120 136970240 ⟨⟨86914711660, 86914711667⟩, ⟨84171167154, 89687658684⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 134348800 135004160 134021120 136970240 ⟨⟨86525413131, 86525413140⟩, ⟨83792780290, 89287248825⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 135004160 135659520 131072000 134021120 ⟨⟨84413268332, 84413268339⟩, ⟨81697808098, 87157804311⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 135659520 136314880 131072000 134021120 ⟨⟨84035139518, 84035139524⟩, ⟨81330408152, 86768749712⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 135004160 135659520 134021120 136970240 ⟨⟨86138425047, 86138425054⟩, ⟨83416617447, 88889237976⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 135659520 136314880 134021120 136970240 ⟨⟨85753722264, 85753722268⟩, ⟨83042654541, 88493599903⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 133693440 134348800 136970240 139919360 ⟨⟨88647303449, 88647303456⟩, ⟨85897446244, 91426489521⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 134348800 135004160 136970240 139919360 ⟨⟨88251442978, 88251442985⟩, ⟨85512507278, 91019509434⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 133693440 134348800 139919360 142868480 ⟨⟨90374159903, 90374159912⟩, ⟨87618045287, 93159529598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 134348800 135004160 139919360 142868480 ⟨⟨89971801019, 89971801028⟩, ⟨87226617001, 92746043558⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 135004160 135659520 136970240 139919360 ⟨⟨87857918505, 87857918512⟩, ⟨85129818102, 90614953670⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 135659520 136314880 136970240 139919360 ⟨⟨87466704723, 87466704725⟩, ⟨84749354460, 90212795833⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 135004160 135659520 139919360 142868480 ⟨⟨89571802967, 89571802976⟩, ⟨86837463561, 92335006422⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 135659520 136314880 139919360 142868480 ⟨⟨89174140283, 89174140287⟩, ⟨86450560550, 91926391649⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 133693440 136314880 131072000 142868480 t = true :=
  ⟨_, (join_sr (m := 136970240) (by decide) (join_su (m := 135004160) (by decide) (join_sr (m := 134021120) (by decide) (join_su (m := 134348800) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 134348800) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 134021120) (by decide) (join_su (m := 135659520) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 135659520) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 135004160) (by decide) (join_sr (m := 139919360) (by decide) (join_su (m := 134348800) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 134348800) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 139919360) (by decide) (join_su (m := 135659520) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 135659520) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (51/320 : ℝ) (13/80 : ℝ) →
    rho ∈ Set.Icc (5/32 : ℝ) (109/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((133693440 : ℤ) : ℝ) / (D : ℝ)) = (51/320 : ℝ) := by norm_num [D]
  have e1 : (((136314880 : ℤ) : ℝ) / (D : ℝ)) = (13/80 : ℝ) := by norm_num [D]
  have e2 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  have e3 : (((142868480 : ℤ) : ℝ) / (D : ℝ)) = (109/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
