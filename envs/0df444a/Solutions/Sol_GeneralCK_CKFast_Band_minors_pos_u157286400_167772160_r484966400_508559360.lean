-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u157286400_167772160_r484966400_508559360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:09:05.439574+00:00
-- url     : https://prove2.me/submissions/c38174ee-72a2-41bc-a899-4bfd5706cab2

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/16, 1/5]`, `ρ ∈ [37/64, 97/160]` by 11 cells of the computing
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
theorem cell0 : cellOK 157286400 159907840 484966400 496762880 ⟨⟨234346036978, 234346036988⟩, ⟨222745371511, 246243120659⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 159907840 162529280 484966400 496762880 ⟨⟨231156352885, 231156352895⟩, ⟨219682255561, 242923850947⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 157286400 159907840 496762880 508559360 ⟨⟨239161014896, 239161014905⟩, ⟨227502188428, 251113447179⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 159907840 162529280 496762880 508559360 ⟨⟨235925593636, 235925593646⟩, ⟨224392696810, 247749242529⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 162529280 165150720 484966400 490864640 ⟨⟨226815435745, 226815435750⟩, ⟨217405634057, 236423715488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 162529280 165150720 490864640 496762880 ⟨⟨229182656216, 229182656221⟩, ⟨219744576379, 238818538067⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 165150720 167772160 484966400 490864640 ⟨⟨223702722692, 223702722700⟩, ⟨214382500528, 233219748379⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 165150720 167772160 490864640 496762880 ⟨⟨226046663853, 226046663863⟩, ⟨216697965346, 235591537915⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 162529280 165150720 496762880 508559360 ⟨⟨232723016130, 232723016135⟩, ⟨221314088766, 244419864255⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 165150720 167772160 496762880 502661120 ⟨⟨228385185954, 228385185964⟩, ⟨219008120958, 237957792743⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 165150720 167772160 502661120 508559360 ⟨⟨230718370859, 230718370869⟩, ⟨221313047275, 240318596695⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 157286400 167772160 484966400 508559360 t = true :=
  ⟨_, (join_su (m := 162529280) (by decide) (join_sr (m := 496762880) (by decide) (join_su (m := 159907840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 159907840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 496762880) (by decide) (join_su (m := 165150720) (by decide) (join_sr (m := 490864640) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 490864640) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 165150720) (by decide) (leaf_ok cell8) (join_sr (m := 502661120) (by decide) (leaf_ok cell9) (leaf_ok cell10)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/16 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (37/64 : ℝ) (97/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((157286400 : ℤ) : ℝ) / (D : ℝ)) = (3/16 : ℝ) := by norm_num [D]
  have e1 : (((167772160 : ℤ) : ℝ) / (D : ℝ)) = (1/5 : ℝ) := by norm_num [D]
  have e2 : (((484966400 : ℤ) : ℝ) / (D : ℝ)) = (37/64 : ℝ) := by norm_num [D]
  have e3 : (((508559360 : ℤ) : ℝ) / (D : ℝ)) = (97/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
