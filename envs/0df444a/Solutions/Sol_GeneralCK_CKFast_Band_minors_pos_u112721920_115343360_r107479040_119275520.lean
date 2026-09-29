-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u112721920_115343360_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:11:28.282405+00:00
-- url     : https://prove2.me/submissions/8b5eb310-291e-40ad-8aab-6965cc9669e7

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [43/320, 11/80]`, `ρ ∈ [41/320, 91/640]` by 16 cells of the computing
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
theorem cell0 : cellOK 112721920 113377280 107479040 110428160 ⟨⟨82764991107, 82764991109⟩, ⟨79681495418, 85886925122⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 113377280 114032640 107479040 110428160 ⟨⟨82357559821, 82357559829⟩, ⟨79288388119, 85464854123⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 112721920 113377280 110428160 113377280 ⟨⟨84800472803, 84800472806⟩, ⟨81709676874, 87929563128⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 113377280 114032640 110428160 113377280 ⟨⟨84384661951, 84384661961⟩, ⟨81308199546, 87499106059⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 114032640 114688000 107479040 110428160 ⟨⟨81953150574, 81953150582⟩, ⟨78898166435, 85045945675⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 114688000 115343360 107479040 110428160 ⟨⟨81551724226, 81551724233⟩, ⟨78510793230, 84630158569⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 114032640 114688000 110428160 113377280 ⟨⟨83971915669, 83971915678⟩, ⟨80909650778, 87071853591⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 114688000 115343360 110428160 113377280 ⟨⟨83562194474, 83562194482⟩, ⟨80513993079, 86647764190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 112721920 113377280 113377280 116326400 ⟨⟨86826828035, 86826828039⟩, ⟨83728832005, 89962974597⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 113377280 114032640 113377280 116326400 ⟨⟨86402745851, 86402745859⟩, ⟨83319091449, 89524241106⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 112721920 113377280 116326400 119275520 ⟨⟨88844164739, 88844164743⟩, ⟨85739066890, 91987269337⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 113377280 114032640 116326400 119275520 ⟨⟨88411917549, 88411917559⟩, ⟨85321168041, 91540367129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 114032640 114688000 113377280 116326400 ⟨⟨85981769357, 85981769364⟩, ⟨82912321010, 89088752839⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 114688000 115343360 113377280 116326400 ⟨⟨85563858750, 85563858759⟩, ⟨82508482861, 88656467958⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 114032640 114688000 116326400 119275520 ⟨⟨87982815803, 87982815812⟩, ⟨84906279521, 91096749381⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 114688000 115343360 116326400 119275520 ⟨⟨87556819398, 87556819408⟩, ⟨84494363180, 90656373971⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 112721920 115343360 107479040 119275520 t = true :=
  ⟨_, (join_sr (m := 113377280) (by decide) (join_su (m := 114032640) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 113377280) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 113377280) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 110428160) (by decide) (join_su (m := 114688000) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 114688000) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 114032640) (by decide) (join_sr (m := 116326400) (by decide) (join_su (m := 113377280) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 113377280) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 116326400) (by decide) (join_su (m := 114688000) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 114688000) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (43/320 : ℝ) (11/80 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((112721920 : ℤ) : ℝ) / (D : ℝ)) = (43/320 : ℝ) := by norm_num [D]
  have e1 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
