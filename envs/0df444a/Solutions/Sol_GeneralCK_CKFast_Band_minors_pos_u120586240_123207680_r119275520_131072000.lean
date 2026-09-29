-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u120586240_123207680_r119275520_131072000
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:20:29.456822+00:00
-- url     : https://prove2.me/submissions/1c7d44ae-950e-41f9-8460-90defc8b640a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [23/160, 47/320]`, `ρ ∈ [91/640, 5/32]` by 16 cells of the computing
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
theorem cell0 : cellOK 120586240 121241600 119275520 122224640 ⟨⟨85770477333, 85770477340⟩, ⟨82822141129, 88753272066⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 121241600 121896960 119275520 122224640 ⟨⟨85365855353, 85365855361⟩, ⟨82430377399, 88335530202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 120586240 121241600 122224640 125173760 ⟨⟨87676992425, 87676992433⟩, ⟨84721823266, 90666508424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 121241600 121896960 122224640 125173760 ⟨⟨87264841009, 87264841017⟩, ⟨84322539095, 90241230455⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 121896960 122552320 119275520 122224640 ⟨⟨84963975043, 84963975051⟩, ⟨82041241706, 87920646780⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 122552320 123207680 119275520 122224640 ⟨⟨84564803385, 84564803389⟩, ⟨81654702576, 87508587183⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 121896960 122552320 122224640 125173760 ⟨⟨86855465324, 86855465332⟩, ⟨83925917349, 89818844613⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 122552320 123207680 122224640 125173760 ⟨⟨86448832107, 86448832109⟩, ⟨83531926302, 89399316045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 120586240 121241600 125173760 128122880 ⟨⟨89575933608, 89575933615⟩, ⟨86614010186, 92572092142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 121241600 121896960 125173760 128122880 ⟨⟨89156339598, 89156339605⟩, ⟨86207291323, 92139365989⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 121241600 128122880 131072000 ⟨⟨91467383347, 91467383357⟩, ⟨88498783038, 94470107014⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 121241600 121896960 128122880 131072000 ⟨⟨91040432196, 91040432203⟩, ⟨88084713876, 94030019177⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 121896960 122552320 125173760 128122880 ⟨⟨88739554318, 88739554327⟩, ⟨85803268232, 91709564572⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 122552320 123207680 125173760 128122880 ⟨⟨88325544274, 88325544278⟩, ⟨85401908940, 91282652819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 121896960 122552320 128122880 131072000 ⟨⟨90616321735, 90616321744⟩, ⟨87673372806, 93592887639⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 122552320 123207680 128122880 131072000 ⟨⟨90195018256, 90195018260⟩, ⟨87264727625, 93158677119⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 120586240 123207680 119275520 131072000 t = true :=
  ⟨_, (join_sr (m := 125173760) (by decide) (join_su (m := 121896960) (by decide) (join_sr (m := 122224640) (by decide) (join_su (m := 121241600) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 121241600) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 122224640) (by decide) (join_su (m := 122552320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 122552320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 121896960) (by decide) (join_sr (m := 128122880) (by decide) (join_su (m := 121241600) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 121241600) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 128122880) (by decide) (join_su (m := 122552320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 122552320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (47/320 : ℝ) →
    rho ∈ Set.Icc (91/640 : ℝ) (5/32 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((120586240 : ℤ) : ℝ) / (D : ℝ)) = (23/160 : ℝ) := by norm_num [D]
  have e1 : (((123207680 : ℤ) : ℝ) / (D : ℝ)) = (47/320 : ℝ) := by norm_num [D]
  have e2 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  have e3 : (((131072000 : ℤ) : ℝ) / (D : ℝ)) = (5/32 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
