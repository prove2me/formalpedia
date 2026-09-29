-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u125829120_146800640_r791674880_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T07:59:11.393874+00:00
-- url     : https://prove2.me/submissions/45bb8c70-8a63-4801-8c19-53a03a79a3f1

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/20, 7/40]`, `ρ ∈ [151/160, 1]` by 16 cells of the computing
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
theorem cell0 : cellOK 125829120 131072000 791674880 803471360 ⟨⟨403877871522, 403877871536⟩, ⟨380325344868, 427991727420⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 125829120 131072000 803471360 815267840 ⟨⟨408643338657, 408643338669⟩, ⟨385014100320, 432820758940⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 131072000 136314880 791674880 803471360 ⟨⟨394862702962, 394862702974⟩, ⟨371643346401, 418654880075⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 131072000 136314880 803471360 815267840 ⟨⟨399570642202, 399570642214⟩, ⟨376270259180, 423431531277⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 125829120 131072000 815267840 827064320 ⟨⟨413397516610, 413397516622⟩, ⟨389691845544, 437638146850⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 125829120 131072000 827064320 838860800 ⟨⟨418141002513, 418141002525⟩, ⟨394359154811, 442444507289⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 131072000 136314880 815267840 827064320 ⟨⟨404267720550, 404267720563⟩, ⟨380886600152, 428196948395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 131072000 136314880 827064320 838860800 ⟨⟨408954504825, 408954504837⟩, ⟨385492913863, 432951717087⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 136314880 141557760 791674880 803471360 ⟨⟨385969447236, 385969447250⟩, ⟨363078002593, 409444130187⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 136314880 141557760 803471360 815267840 ⟨⟨390617660421, 390617660432⟩, ⟨367641210198, 414165846188⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 141557760 146800640 791674880 803471360 ⟨⟨377192402583, 377192402590⟩, ⟨354623839464, 400353624148⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 141557760 146800640 803471360 815267840 ⟨⟨381778810094, 381778810099⟩, ⟨359121583110, 405017982982⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 136314880 141557760 815267840 827064320 ⟨⟨395255446383, 395255446398⟩, ⟨372194284329, 418876749786⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 136314880 141557760 827064320 838860800 ⟨⟨399883342306, 399883342317⟩, ⟨376737740600, 423577396650⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 141557760 146800640 815267840 827064320 ⟨⟨386355226962, 386355226968⟩, ⟨363609629691, 409671960048⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 141557760 146800640 827064320 838860800 ⟨⟨390922161464, 390922161472⟩, ⟨368088466722, 414316081629⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 125829120 146800640 791674880 838860800 t = true :=
  ⟨_, (join_su (m := 136314880) (by decide) (join_sr (m := 815267840) (by decide) (join_su (m := 131072000) (by decide) (join_sr (m := 803471360) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 803471360) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 131072000) (by decide) (join_sr (m := 827064320) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 827064320) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 815267840) (by decide) (join_su (m := 141557760) (by decide) (join_sr (m := 803471360) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 803471360) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 141557760) (by decide) (join_sr (m := 827064320) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 827064320) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/20 : ℝ) (7/40 : ℝ) →
    rho ∈ Set.Icc (151/160 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e1 : (((146800640 : ℤ) : ℝ) / (D : ℝ)) = (7/40 : ℝ) := by norm_num [D]
  have e2 : (((791674880 : ℤ) : ℝ) / (D : ℝ)) = (151/160 : ℝ) := by norm_num [D]
  have e3 : (((838860800 : ℤ) : ℝ) / (D : ℝ)) = (1 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
