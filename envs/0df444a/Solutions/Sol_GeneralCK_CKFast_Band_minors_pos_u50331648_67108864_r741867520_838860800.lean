-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u50331648_67108864_r741867520_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T10:21:57.638485+00:00
-- url     : https://prove2.me/submissions/2fd79707-ddfc-4dea-82ec-fc5e9ab92af6

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/50, 2/25]`, `ρ ∈ [283/320, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 50331648 54525952 741867520 766115840 ⟨⟨534053339308, 534053339318⟩, ⟨501761168490, 566661389844⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 54525952 58720256 741867520 766115840 ⟨⟨524531817049, 524531817065⟩, ⟨492741815329, 556677448480⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 50331648 54525952 766115840 790364160 ⟨⟨544948178163, 544948178169⟩, ⟨512811422888, 577331147375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 54525952 58720256 766115840 790364160 ⟨⟨535421340316, 535421340331⟩, ⟨503762823036, 567367946813⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 58720256 62914560 741867520 766115840 ⟨⟨515225953317, 515225953331⟩, ⟨483924639728, 546918839838⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 62914560 67108864 741867520 766115840 ⟨⟨506120485036, 506120485050⟩, ⟨475295691131, 537369439761⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 58720256 62914560 766115840 790364160 ⟨⟨526102146972, 526102146988⟩, ⟨494909709127, 557620766092⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 62914560 67108864 766115840 790364160 ⟨⟨516975864089, 516975864103⟩, ⟨486238578560, 548074081443⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 50331648 54525952 790364160 814612480 ⟨⟨555770778749, 555770778758⟩, ⟨523782416374, 587937677075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 54525952 58720256 790364160 814612480 ⟨⟨546238078429, 546238078443⟩, ⟨514705031650, 577993486909⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 50331648 54525952 814612480 838860800 ⟨⟨566530473153, 566530473161⟩, ⟨534683674077, 598489845280⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 54525952 58720256 814612480 838860800 ⟨⟨556991230266, 556991230281⟩, ⟨525577759206, 588562899219⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 58720256 62914560 790364160 814612480 ⟨⟨536905314963, 536905314977⟩, ⟨505816652098, 568256412739⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 62914560 67108864 790364160 814612480 ⟨⟨527758249625, 527758249639⟩, ⟨497104197096, 558711490044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 58720256 62914560 814612480 838860800 ⟨⟨547644500047, 547644500062⟩, ⟨516654566591, 578834539911⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 62914560 67108864 814612480 838860800 ⟨⟨538476509054, 538476509069⟩, ⟨507901414230, 569290325732⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 50331648 67108864 741867520 838860800 t = true :=
  ⟨_, (join_sr (m := 790364160) (by decide) (join_su (m := 58720256) (by decide) (join_sr (m := 766115840) (by decide) (join_su (m := 54525952) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 54525952) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 766115840) (by decide) (join_su (m := 62914560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_su (m := 62914560) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_su (m := 58720256) (by decide) (join_sr (m := 814612480) (by decide) (join_su (m := 54525952) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_su (m := 54525952) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_sr (m := 814612480) (by decide) (join_su (m := 62914560) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_su (m := 62914560) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/50 : ℝ) (2/25 : ℝ) →
    rho ∈ Set.Icc (283/320 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((50331648 : ℤ) : ℝ) / (D : ℝ)) = (3/50 : ℝ) := by norm_num [D]
  have e1 : (((67108864 : ℤ) : ℝ) / (D : ℝ)) = (2/25 : ℝ) := by norm_num [D]
  have e2 : (((741867520 : ℤ) : ℝ) / (D : ℝ)) = (283/320 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
