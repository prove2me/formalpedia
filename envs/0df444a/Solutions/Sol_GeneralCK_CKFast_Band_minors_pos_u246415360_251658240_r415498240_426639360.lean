-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u246415360_251658240_r415498240_426639360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T14:14:32.145074+00:00
-- url     : https://prove2.me/submissions/6bb349c4-c553-4e8d-9b13-0b2bf78d6bad

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [47/160, 3/10]`, `ρ ∈ [317/640, 651/1280]` by 15 cells of the computing
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
theorem cell0 : cellOK 246415360 247726080 415498240 418283520 ⟨⟨120746050453, 120746050459⟩, ⟨117361056127, 124167890660⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 246415360 247726080 418283520 421068800 ⟨⟨121512010811, 121512010819⟩, ⟨118120396984, 124940504312⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 247726080 249036800 415498240 418283520 ⟨⟨119688197731, 119688197737⟩, ⟨116316785478, 123096296060⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 247726080 249036800 418283520 421068800 ⟨⟨120448122387, 120448122394⟩, ⟨117070111504, 123862853889⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 246415360 247726080 421068800 426639360 ⟨⟨122660170832, 122660170839⟩, ⟨118759303968, 126611378111⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 247726080 249036800 421068800 423854080 ⟨⟨121207640411, 121207640418⟩, ⟨117823031632, 124629004190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 247726080 249036800 423854080 426639360 ⟨⟨121966753911, 121966753919⟩, ⟨118575547959, 125394749080⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 249036800 250347520 415498240 418283520 ⟨⟨118633950500, 118633950508⟩, ⟨115276026435, 122028402100⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 249036800 250347520 418283520 421068800 ⟨⟨119387843245, 119387843251⟩, ⟨116023341683, 122788907620⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 250347520 251658240 415498240 418283520 ⟨⟨117583263578, 117583263585⟩, ⟨114238734875, 120964162528⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 250347520 251658240 418283520 421068800 ⟨⟨118331128222, 118331128230⟩, ⟨114980043410, 121718619279⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 249036800 250347520 421068800 423854080 ⟨⟨120141339188, 120141339196⟩, ⟨116770260727, 123549015583⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 249036800 250347520 423854080 426639360 ⟨⟨120894440381, 120894440387⟩, ⟨117516785607, 124308728044⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 250347520 251658240 421068800 423854080 ⟨⟨119078605725, 119078605732⟩, ⟨115720965269, 122472688267⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 250347520 251658240 423854080 426639360 ⟨⟨119825698078, 119825698085⟩, ⟨116461502434, 123226371494⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 246415360 251658240 415498240 426639360 t = true :=
  ⟨_, (join_su (m := 249036800) (by decide) (join_sr (m := 421068800) (by decide) (join_su (m := 247726080) (by decide) (join_sr (m := 418283520) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 418283520) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 247726080) (by decide) (leaf_ok cell4) (join_sr (m := 423854080) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 421068800) (by decide) (join_su (m := 250347520) (by decide) (join_sr (m := 418283520) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 418283520) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 250347520) (by decide) (join_sr (m := 423854080) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 423854080) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (47/160 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (317/640 : ℝ) (651/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((246415360 : ℤ) : ℝ) / (D : ℝ)) = (47/160 : ℝ) := by norm_num [D]
  have e1 : (((251658240 : ℤ) : ℝ) / (D : ℝ)) = (3/10 : ℝ) := by norm_num [D]
  have e2 : (((415498240 : ℤ) : ℝ) / (D : ℝ)) = (317/640 : ℝ) := by norm_num [D]
  have e3 : (((426639360 : ℤ) : ℝ) / (D : ℝ)) = (651/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
