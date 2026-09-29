-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u247726080_249036800_r125829120_128614400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T09:41:51.838515+00:00
-- url     : https://prove2.me/submissions/4c7c269e-38f6-4846-b5c4-9290e9dc2399

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [189/640, 19/64]`, `ρ ∈ [3/20, 157/1024]` by 16 cells of the computing
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
theorem cell0 : cellOK 247726080 248053760 125829120 126525440 ⟨⟨37822634238, 37822634244⟩, ⟨37149454406, 38497834874⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 247726080 248053760 126525440 127221760 ⟨⟨38027231858, 38027231863⟩, ⟨37353629324, 38702855970⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 248053760 248381440 125829120 126525440 ⟨⟨37732885589, 37732885592⟩, ⟨37060366184, 38407422450⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 248053760 248381440 126525440 127221760 ⟨⟨37937016140, 37937016141⟩, ⟨37264074642, 38611975866⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 247726080 248053760 127221760 127918080 ⟨⟨38231787175, 38231787180⟩, ⟨37557761968, 38907834733⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247726080 248053760 127918080 128614400 ⟨⟨38436300238, 38436300243⟩, ⟨37761852387, 39112771212⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 248053760 248381440 127221760 127918080 ⟨⟨38141104672, 38141104674⟩, ⟨37467741112, 38816487237⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 248053760 248381440 127918080 128614400 ⟨⟨38345151233, 38345151235⟩, ⟨37671365638, 39020956607⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 248381440 248709120 125829120 126525440 ⟨⟨37643257126, 37643257131⟩, ⟨36971396573, 38317131802⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 248381440 248709120 126525440 127221760 ⟨⟨37846921110, 37846921115⟩, ⟨37174639075, 38521218045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 248709120 249036800 125829120 126525440 ⟨⟨37553748396, 37553748401⟩, ⟨36882545126, 38226962465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 248709120 249036800 126525440 127221760 ⟨⟨37756946318, 37756946323⟩, ⟨37085322174, 38430582038⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 248381440 248709120 127221760 127918080 ⟨⟨38050543360, 38050543365⟩, ⟨37377839870, 38725262525⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 248381440 248709120 127918080 128614400 ⟨⟨38254123920, 38254123926⟩, ⟨37580999002, 38929265288⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 248709120 249036800 127221760 127918080 ⟨⟨37960102785, 37960102790⟩, ⟨37288057794, 38634160129⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 248709120 249036800 127918080 128614400 ⟨⟨38163217842, 38163217848⟩, ⟨37490752032, 38837696783⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 247726080 249036800 125829120 128614400 t = true :=
  ⟨_, (join_su (m := 248381440) (by decide) (join_sr (m := 127221760) (by decide) (join_su (m := 248053760) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 126525440) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 248053760) (by decide) (join_sr (m := 127918080) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 127918080) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 127221760) (by decide) (join_su (m := 248709120) (by decide) (join_sr (m := 126525440) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 126525440) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 248709120) (by decide) (join_sr (m := 127918080) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 127918080) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (189/640 : ℝ) (19/64 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (157/1024 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((247726080 : ℤ) : ℝ) / (D : ℝ)) = (189/640 : ℝ) := by norm_num [D]
  have e1 : (((249036800 : ℤ) : ℝ) / (D : ℝ)) = (19/64 : ℝ) := by norm_num [D]
  have e2 : (((125829120 : ℤ) : ℝ) / (D : ℝ)) = (3/20 : ℝ) := by norm_num [D]
  have e3 : (((128614400 : ℤ) : ℝ) / (D : ℝ)) = (157/1024 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
