-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u228065280_229376000_r142540800_148111360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:59:49.316681+00:00
-- url     : https://prove2.me/submissions/6ba940d2-e839-4da8-bbe6-b74f57eed493

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [87/320, 35/128]`, `ρ ∈ [87/512, 113/640]` by 14 cells of the computing
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
theorem cell0 : cellOK 228065280 228392960 142540800 143933440 ⟨⟨49151519536, 49151519541⟩, ⟨48292094882, 50014212484⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 228392960 228720640 142540800 143933440 ⟨⟨49041497829, 49041497832⟩, ⟨48183182058, 49903075012⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 228065280 228392960 143933440 145326080 ⟨⟨49615662199, 49615662204⟩, ⟨48755238035, 50479355785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 228392960 228720640 143933440 145326080 ⟨⟨49504658581, 49504658584⟩, ⟨48645344824, 50367234881⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 228720640 229048320 142540800 143933440 ⟨⟨48931641916, 48931641921⟩, ⟨48074432402, 49792105983⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 229048320 229376000 142540800 143933440 ⟨⟨48821951161, 48821951168⟩, ⟨47965845294, 49681304746⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 228720640 229048320 143933440 145326080 ⟨⟨49393821883, 49393821889⟩, ⟨48535615909, 50255283552⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 229048320 229376000 143933440 145326080 ⟨⟨49283151470, 49283151476⟩, ⟨48426050666, 50143501142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 228065280 228392960 145326080 146718720 ⟨⟨50079562738, 50079562743⟩, ⟨49218139608, 50944256415⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 228392960 228720640 145326080 146718720 ⟨⟨49967578715, 49967578716⟩, ⟨49107267511, 50831153593⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 228065280 228720640 146718720 148111360 ⟨⟨50486719104, 50486719110⟩, ⟨49029898621, 51952587549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 228720640 229048320 145326080 146718720 ⟨⟨49855762732, 49855762737⟩, ⟨48996560828, 50718221469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 229048320 229376000 145326080 146718720 ⟨⟨49744114152, 49744114158⟩, ⟨48886018934, 50605459384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 228720640 229376000 146718720 148111360 ⟨⟨50261131399, 50261131405⟩, ⟨48807438629, 51723839932⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 228065280 229376000 142540800 148111360 t = true :=
  ⟨_, (join_sr (m := 145326080) (by decide) (join_su (m := 228720640) (by decide) (join_sr (m := 143933440) (by decide) (join_su (m := 228392960) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 228392960) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 143933440) (by decide) (join_su (m := 229048320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 229048320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 228720640) (by decide) (join_sr (m := 146718720) (by decide) (join_su (m := 228392960) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (leaf_ok cell10)) (join_sr (m := 146718720) (by decide) (join_su (m := 229048320) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (leaf_ok cell13))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (87/320 : ℝ) (35/128 : ℝ) →
    rho ∈ Set.Icc (87/512 : ℝ) (113/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((228065280 : ℤ) : ℝ) / (D : ℝ)) = (87/320 : ℝ) := by norm_num [D]
  have e1 : (((229376000 : ℤ) : ℝ) / (D : ℝ)) = (35/128 : ℝ) := by norm_num [D]
  have e2 : (((142540800 : ℤ) : ℝ) / (D : ℝ)) = (87/512 : ℝ) := by norm_num [D]
  have e3 : (((148111360 : ℤ) : ℝ) / (D : ℝ)) = (113/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
