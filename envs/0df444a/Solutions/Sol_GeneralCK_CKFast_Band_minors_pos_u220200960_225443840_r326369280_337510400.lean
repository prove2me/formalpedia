-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u220200960_225443840_r326369280_337510400
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T07:09:05.374987+00:00
-- url     : https://prove2.me/submissions/fe1c9cb2-e273-4756-828e-353b2e441e25

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [21/80, 43/160]`, `ρ ∈ [249/640, 103/256]` by 15 cells of the computing
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
theorem cell0 : cellOK 220200960 221511680 326369280 329154560 ⟨⟨113967880666, 113967880674⟩, ⟨110515280770, 117460206767⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 220200960 221511680 329154560 331939840 ⟨⟨114878359123, 114878359129⟩, ⟨111418634943, 118377832164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 221511680 222822400 326369280 329154560 ⟨⟨113030798894, 113030798902⟩, ⟨109593340529, 116507760554⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 221511680 222822400 329154560 331939840 ⟨⟨113934674356, 113934674363⟩, ⟨110490112957, 117418762729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 220200960 221511680 331939840 337510400 ⟨⟨116242609109, 116242609115⟩, ⟨112177545689, 120363867395⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 221511680 222822400 331939840 334725120 ⟨⟨114837783625, 114837783631⟩, ⟨111386124199, 118328993467⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 221511680 222822400 334725120 337510400 ⟨⟨115740130808, 115740130814⟩, ⟨112281378329, 119238456900⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 222822400 224133120 326369280 329154560 ⟨⟨112098132548, 112098132556⟩, ⟨108675685679, 115559862142⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 222822400 224133120 329154560 331939840 ⟨⟨112995416062, 112995416070⟩, ⟨109565887699, 116464251828⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 224133120 225443840 326369280 329154560 ⟨⟨111169822823, 111169822830⟩, ⟨107762259136, 114616450966⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 224133120 225443840 329154560 331939840 ⟨⟨112060525411, 112060525417⟩, ⟨108645902051, 115514238877⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 222822400 224133120 331939840 334725120 ⟨⟨113891950373, 113891950380⟩, ⟨110455345283, 117367887306⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 222822400 224133120 334725120 337510400 ⟨⟨114787739473, 114787739481⟩, ⟨111344062393, 118270772598⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 224133120 225443840 331939840 334725120 ⟨⟨112950495491, 112950495497⟩, ⟨109528816991, 116411289516⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 224133120 225443840 334725120 337510400 ⟨⟨113839736950, 113839736956⟩, ⟨110411007815, 117307606795⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 220200960 225443840 326369280 337510400 t = true :=
  ⟨_, (join_su (m := 222822400) (by decide) (join_sr (m := 331939840) (by decide) (join_su (m := 221511680) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 329154560) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 221511680) (by decide) (leaf_ok cell4) (join_sr (m := 334725120) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_sr (m := 331939840) (by decide) (join_su (m := 224133120) (by decide) (join_sr (m := 329154560) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 329154560) (by decide) (leaf_ok cell9) (leaf_ok cell10))) (join_su (m := 224133120) (by decide) (join_sr (m := 334725120) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_sr (m := 334725120) (by decide) (leaf_ok cell13) (leaf_ok cell14)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (21/80 : ℝ) (43/160 : ℝ) →
    rho ∈ Set.Icc (249/640 : ℝ) (103/256 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e1 : (((225443840 : ℤ) : ℝ) / (D : ℝ)) = (43/160 : ℝ) := by norm_num [D]
  have e2 : (((326369280 : ℤ) : ℝ) / (D : ℝ)) = (249/640 : ℝ) := by norm_num [D]
  have e3 : (((337510400 : ℤ) : ℝ) / (D : ℝ)) = (103/256 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
