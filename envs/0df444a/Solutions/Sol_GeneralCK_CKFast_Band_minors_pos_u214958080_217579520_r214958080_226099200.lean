-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u214958080_217579520_r214958080_226099200
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T06:13:01.855871+00:00
-- url     : https://prove2.me/submissions/9abd11cd-b1e2-4b60-8020-a6d2035a37e5

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [41/160, 83/320]`, `ρ ∈ [41/160, 69/256]` by 16 cells of the computing
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
theorem cell0 : cellOK 214958080 215613440 214958080 217743360 ⟨⟨79691906197, 79691906203⟩, ⟨77775344089, 81622839462⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 215613440 216268800 214958080 217743360 ⟨⟨79354555379, 79354555384⟩, ⟨77443148306, 81280275352⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 214958080 215613440 217743360 220528640 ⟨⟨80669131743, 80669131750⟩, ⟨78748490329, 82604148110⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 215613440 216268800 217743360 220528640 ⟨⟨80328023549, 80328023556⟩, ⟨78412546692, 82257817302⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 216268800 216924160 214958080 217743360 ⟨⟨79018195563, 79018195570⟩, ⟨77111919077, 80938727070⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 216924160 217579520 214958080 217743360 ⟨⟨78682819456, 78682819463⟩, ⟨76781649295, 80598187130⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 216268800 216924160 217743360 220528640 ⟨⟨79987913018, 79987913025⟩, ⟨78077576283, 81912508961⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 216924160 217579520 217743360 220528640 ⟨⟨79648792820, 79648792827⟩, ⟨77743571961, 81568215571⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 215613440 220528640 223313920 ⟨⟨81645288230, 81645288237⟩, ⟨79720573169, 83584381957⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 215613440 216268800 220528640 223313920 ⟨⟨81300434937, 81300434943⟩, ⟨79380893843, 83234296835⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 214958080 215613440 223313920 226099200 ⟨⟨82620381382, 82620381388⟩, ⟨80691598296, 84563546759⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 215613440 216268800 223313920 226099200 ⟨⟨82271795179, 82271795186⟩, ⟨80348195365, 84209719624⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 216268800 216924160 220528640 223313920 ⟨⟨80956585847, 80956585854⟩, ⟨79042194305, 82885240702⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 216924160 217579520 220528640 223313920 ⟨⟨80613733601, 80613733608⟩, ⟨78704467381, 82537206011⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 216268800 216924160 223313920 226099200 ⟨⟨81924219606, 81924219613⟩, ⟨80005778667, 83856927882⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 216924160 217579520 223313920 226099200 ⟨⟨81577647275, 81577647281⟩, ⟨79664340996, 83505163959⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 214958080 217579520 214958080 226099200 t = true :=
  ⟨_, (join_sr (m := 220528640) (by decide) (join_su (m := 216268800) (by decide) (join_sr (m := 217743360) (by decide) (join_su (m := 215613440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 215613440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 217743360) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 216924160) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 216268800) (by decide) (join_sr (m := 223313920) (by decide) (join_su (m := 215613440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 215613440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 223313920) (by decide) (join_su (m := 216924160) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 216924160) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (41/160 : ℝ) (83/320 : ℝ) →
    rho ∈ Set.Icc (41/160 : ℝ) (69/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e1 : (((217579520 : ℤ) : ℝ) / (D : ℝ)) = (83/320 : ℝ) := by norm_num [D]
  have e2 : (((214958080 : ℤ) : ℝ) / (D : ℝ)) = (41/160 : ℝ) := by norm_num [D]
  have e3 : (((226099200 : ℤ) : ℝ) / (D : ℝ)) = (69/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
