-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u115343360_125829120_r367001600_390594560
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:44:01.550985+00:00
-- url     : https://prove2.me/submissions/438732bd-07e8-45db-8f8d-612c8cf249ce

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [11/80, 3/20]`, `ρ ∈ [7/16, 149/320]` by 14 cells of the computing
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
theorem cell0 : cellOK 115343360 117964800 367001600 372899840 ⟨⟨231859435276, 231859435285⟩, ⟨220983991475, 243005124609⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 115343360 117964800 372899840 378798080 ⟨⟨234850103903, 234850103914⟩, ⟨223949958640, 246018502762⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 117964800 120586240 367001600 372899840 ⟨⟨228464950838, 228464950849⟩, ⟨217727925599, 239468239856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 117964800 120586240 372899840 378798080 ⟨⟨231429213661, 231429213672⟩, ⟨220666803169, 242456011513⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 115343360 117964800 378798080 390594560 ⟨⟨239310437952, 239310437963⟩, ⟨225745592917, 253283539526⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 117964800 120586240 378798080 390594560 ⟨⟨235850718032, 235850718041⟩, ⟨222470791468, 249632544907⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 120586240 123207680 367001600 372899840 ⟨⟨225127612147, 225127612157⟩, ⟨214525607838, 235991989412⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 120586240 123207680 372899840 378798080 ⟨⟨228065283265, 228065283277⟩, ⟨217437261623, 238953911529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 123207680 125829120 367001600 372899840 ⟨⟨221845483980, 221845483987⟩, ⟨211375229823, 232574308996⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 123207680 125829120 372899840 378798080 ⟨⟨224756396376, 224756396383⟩, ⟨214259541537, 235510160668⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 123207680 378798080 384696320 ⟨⟨230990047467, 230990047478⟩, ⟨220336285524, 241902651449⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 120586240 123207680 384696320 390594560 ⟨⟨233902137076, 233902137087⟩, ⟨223222904760, 244838448631⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 123207680 125829120 378798080 384696320 ⟨⟨227654801073, 227654801076⟩, ⟨217131616321, 238433234519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 123207680 125829120 384696320 390594560 ⟨⟨230540920178, 230540920185⟩, ⟨219991669529, 241343759462⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 115343360 125829120 367001600 390594560 t = true :=
  ⟨_, (join_su (m := 120586240) (by decide) (join_sr (m := 378798080) (by decide) (join_su (m := 117964800) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 372899840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 117964800) (by decide) (leaf_ok cell4) (leaf_ok cell5))) (join_sr (m := 378798080) (by decide) (join_su (m := 123207680) (by decide) (join_sr (m := 372899840) (by decide) (leaf_ok cell6) (leaf_ok cell7)) (join_sr (m := 372899840) (by decide) (leaf_ok cell8) (leaf_ok cell9))) (join_su (m := 123207680) (by decide) (join_sr (m := 384696320) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_sr (m := 384696320) (by decide) (leaf_ok cell12) (leaf_ok cell13)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/80 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (7/16 : ℝ) (149/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((115343360 : ℤ) : ℝ) / (D : ℝ)) = (11/80 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((367001600 : ℤ) : ℝ) / (D : ℝ)) = (7/16 : ℝ) := by norm_num [D]
  have e3 : (((390594560 : ℤ) : ℝ) / (D : ℝ)) = (149/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
