-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u201850880_204472320_r203816960_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:18:18.631384+00:00
-- url     : https://prove2.me/submissions/650197d9-887f-4e52-a1d6-69da35b31a5f

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [77/320, 39/160]`, `ρ ∈ [311/1280, 41/160]` by 16 cells of the computing
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
theorem cell0 : cellOK 201850880 202506240 203816960 206602240 ⟨⟨82430012019, 82430012025⟩, ⟨80422053682, 84453593255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 202506240 203161600 203816960 206602240 ⟨⟨82086945465, 82086945471⟩, ⟨80084635817, 84104810437⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 201850880 202506240 206602240 209387520 ⟨⟨83489273178, 83489273186⟩, ⟨81477016463, 85517152366⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 202506240 203161600 206602240 209387520 ⟨⟨83142248851, 83142248858⟩, ⟨81135650438, 85164402424⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 203161600 203816960 203816960 206602240 ⟨⟨81744999540, 81744999546⟩, ⟨79748309859, 83757177436⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 203816960 204472320 203816960 206602240 ⟨⟨81404165675, 81404165681⟩, ⟨79413067473, 83410685446⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 203161600 203816960 206602240 209387520 ⟨⟨82796353030, 82796353038⟩, ⟨80795384223, 84812810146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 203816960 204472320 206602240 209387520 ⟨⟨82451577109, 82451577116⟩, ⟨80456209442, 84462366690⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 201850880 202506240 209387520 212172800 ⟨⟨84547162515, 84547162522⟩, ⟨82530615756, 86579331215⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 202506240 203161600 209387520 212172800 ⟨⟨84196195700, 84196195708⟩, ⟨82185316719, 86222629575⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 201850880 202506240 212172800 214958080 ⟨⟨85603687875, 85603687881⟩, ⟨83582859355, 87640137705⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 202506240 203161600 212172800 214958080 ⟨⟨85248793747, 85248793755⟩, ⟨83233642337, 87279499682⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 203161600 203816960 209387520 212172800 ⟨⟨83846365127, 83846365133⟩, ⟨81841125249, 85867093303⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 203816960 204472320 209387520 212172800 ⟨⟨83497662146, 83497662152⟩, ⟨81498032935, 85512713518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 203161600 203816960 212172800 214958080 ⟨⟨84895043449, 84895043455⟩, ⟨82885540503, 86920034585⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 203816960 204472320 212172800 214958080 ⟨⟨84542428296, 84542428303⟩, ⟨82538545406, 86561733496⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 201850880 204472320 203816960 214958080 t = true :=
  ⟨_, (join_sr (m := 209387520) (by decide) (join_su (m := 203161600) (by decide) (join_sr (m := 206602240) (by decide) (join_su (m := 202506240) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 202506240) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 206602240) (by decide) (join_su (m := 203816960) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 203816960) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 203161600) (by decide) (join_sr (m := 212172800) (by decide) (join_su (m := 202506240) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 202506240) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 212172800) (by decide) (join_su (m := 203816960) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 203816960) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (77/320 : ℝ) (39/160 : ℝ) →
    rho ∈ Set.Icc (311/1280 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((201850880 : ℤ) : ℝ) / (D : ℝ)) = (77/320 : ℝ) := by norm_num [D]
  have e1 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e2 : (((203816960 : ℤ) : ℝ) / (D : ℝ)) = (311/1280 : ℝ) := by norm_num [D]
  have e3 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
