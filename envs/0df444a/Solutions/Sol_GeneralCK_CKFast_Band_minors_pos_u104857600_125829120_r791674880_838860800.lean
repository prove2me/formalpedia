-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u104857600_125829120_r791674880_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T06:52:52.353065+00:00
-- url     : https://prove2.me/submissions/0a567a01-9326-4819-a073-3438ff342d86

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/8, 3/20]`, `ρ ∈ [151/160, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 104857600 110100480 791674880 803471360 ⟨⟨441287707387, 441287707399⟩, ⟨416344381972, 466733813794⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 104857600 110100480 803471360 815267840 ⟨⟨446258623963, 446258623976⟩, ⟨421259532612, 471743820785⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 110100480 115343360 791674880 803471360 ⟨⟨431718549572, 431718549584⟩, ⟨407132281781, 456824336161⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 110100480 115343360 803471360 815267840 ⟨⟨436642096053, 436642096065⟩, ⟨411994237175, 461793708115⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 104857600 110100480 815267840 827064320 ⟨⟨451216652298, 451216652311⟩, ⟨426161964039, 476740744140⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 104857600 110100480 827064320 838860800 ⟨⟨456162515612, 456162515625⟩, ⟨431052376173, 481725324149⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 110100480 115343360 815267840 827064320 ⟨⟨441553130045, 441553130060⟩, ⟨416843888624, 466750318049⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 110100480 115343360 827064320 838860800 ⟨⟨446452342765, 446452342778⟩, ⟨421681903789, 471694875221⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 115343360 120586240 791674880 803471360 ⟨⟨422298924012, 422298924020⟩, ⟨398063241909, 447069384594⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 115343360 120586240 803471360 815267840 ⟨⟨427172335846, 427172335851⟩, ⟨402869642478, 451994934058⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 120586240 125829120 791674880 803471360 ⟨⟨413021078047, 413021078059⟩, ⟨389129870352, 437460965717⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 120586240 125829120 803471360 815267840 ⟨⟨417841748051, 417841748063⟩, ⟨393878494835, 442339680667⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 115343360 120586240 815267840 827064320 ⟨⟨432033629436, 432033629445⟩, ⟨407664164269, 456908071828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 115343360 120586240 827064320 838860800 ⟨⟨436883464230, 436883464237⟩, ⟨412447443185, 461809475994⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 120586240 125829120 815267840 827064320 ⟨⟨422650708730, 422650708742⟩, ⟨398615672652, 447206358168⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 120586240 125829120 827064320 838860800 ⟨⟨427448588122, 427448588134⟩, ⟨403342008554, 452061645214⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 104857600 125829120 791674880 838860800 t = true :=
  ⟨_, (join_su (m := 115343360) (by decide) (join_sr (m := 815267840) (by decide) (join_su (m := 110100480) (by decide) (join_sr (m := 803471360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 803471360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 110100480) (by decide) (join_sr (m := 827064320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 827064320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 815267840) (by decide) (join_su (m := 120586240) (by decide) (join_sr (m := 803471360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 803471360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 120586240) (by decide) (join_sr (m := 827064320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 827064320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/8 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (151/160 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((104857600 : ℤ) : ℝ) / (D : ℝ)) = (1/8 : ℝ) := by norm_num [D]
  have e1 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e2 : (((791674880 : ℤ) : ℝ) / (D : ℝ)) = (151/160 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
