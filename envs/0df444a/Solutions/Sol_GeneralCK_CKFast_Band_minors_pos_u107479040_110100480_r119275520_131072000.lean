-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u107479040_110100480_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:11:09.540322+00:00
-- url     : https://prove2.me/submissions/bb5d24ce-1e1c-46cf-9299-4d0cf3ea14f6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/320, 21/160]`, `ρ ∈ [91/640, 5/32]` by 12 cells of the computing
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
theorem cell0 : cellOK 107479040 108134400 119275520 122224640 ⟨⟨94494754868, 94494754878⟩, ⟨91262729344, 97767219864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 108134400 108789760 119275520 122224640 ⟨⟨94027434806, 94027434815⟩, ⟨90810914663, 97284057406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 107479040 108134400 122224640 125173760 ⟨⟨96559402371, 96559402379⟩, ⟨93320453460, 99838621035⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 108134400 108789760 122224640 125173760 ⟨⟨96083818016, 96083818024⟩, ⟨92860373990, 99347198295⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 108789760 109445120 119275520 122224640 ⟨⟨93563648340, 93563648350⟩, ⟨90362481981, 96804584571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 109445120 110100480 119275520 122224640 ⟨⟨93103348999, 93103349004⟩, ⟨89917387094, 96328752538⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 108789760 109445120 122224640 125173760 ⟨⟨95611806485, 95611806493⟩, ⟨92403716380, 98859503698⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 109445120 110100480 122224640 125173760 ⟨⟨95143321042, 95143321044⟩, ⟨91950436142, 98375488175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 107479040 108789760 125173760 128122880 ⟨⟨98372167455, 98372167461⟩, ⟨93323246081, 103518920450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 107479040 108789760 128122880 131072000 ⟨⟨100413786215, 100413786221⟩, ⟨95352811212, 105572253004⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 108789760 110100480 125173760 128122880 ⟨⟨97411903083, 97411903091⟩, ⟨92407573954, 102512561627⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 108789760 110100480 128122880 131072000 ⟨⟨99437508802, 99437508812⟩, ⟨94421132264, 104549889842⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 107479040 110100480 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 108789760) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 108134400) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 108134400) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 109445120) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 109445120) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 108789760) (by decide) (join_sr (m := 128122880) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 128122880) (by decide) (leaf_ok cell10) (leaf_ok cell11))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/320 : ℝ) (21/160 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e1 : (((110100480 : ℤ) : ℝ) / (D : ℝ)) = (21/160 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
