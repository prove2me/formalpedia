-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u188743680_193986560_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:32:49.472321+00:00
-- url     : https://prove2.me/submissions/a745dfde-9383-46ed-858b-7aa055107a0a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [9/40, 37/160]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 188743680 190054400 259522560 262307840 ⟨⟨111806493318, 111806493326⟩, ⟨108130874807, 115528139853⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 188743680 190054400 262307840 265093120 ⟨⟨112912450429, 112912450435⟩, ⟨109228983354, 116641943174⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 190054400 191365120 259522560 262307840 ⟨⟨110916332043, 110916332051⟩, ⟨107259205018, 114619154254⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 190054400 191365120 262307840 265093120 ⟨⟨112014738360, 112014738367⟩, ⟨108349783443, 115725387831⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 188743680 190054400 265093120 267878400 ⟨⟨114016903184, 114016903190⟩, ⟨110325602401, 117754226912⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 188743680 190054400 267878400 270663680 ⟨⟨115119860782, 115119860790⟩, ⟨111420741049, 118865000375⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 190054400 191365120 265093120 267878400 ⟨⟨113111671453, 113111671461⟩, ⟨109438903046, 116830133418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 190054400 191365120 267878400 270663680 ⟨⟨114207140275, 114207140283⟩, ⟨110526572683, 117933400071⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 191365120 192675840 259522560 262307840 ⟨⟨110031915541, 110031915548⟩, ⟨106393085135, 113716112672⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 191365120 192675840 262307840 265093120 ⟨⟨111122793137, 111122793144⟩, ⟨107476155947, 114814798097⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 192675840 193986560 259522560 262307840 ⟨⟨109153158262, 109153158264⟩, ⟨105532432700, 112818926384⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 192675840 193986560 262307840 265093120 ⟨⟨110236529109, 110236529113⟩, ⟨106608018292, 113910085164⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 191365120 192675840 265093120 267878400 ⟨⟨112212228104, 112212228110⟩, ⟨108557798085, 115912026577⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 191365120 192675840 267878400 270663680 ⟨⟨113300229147, 113300229155⟩, ⟨109638020163, 117007806918⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 192675840 193986560 265093120 267878400 ⟨⟨111318487387, 111318487392⟩, ⟨107682204834, 114999817503⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 192675840 193986560 267878400 270663680 ⟨⟨112399041568, 112399041573⟩, ⟨108755000706, 116088131966⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 188743680 193986560 259522560 270663680 t = true :=
  ⟨_, (join_su (m := 191365120) (by decide) (join_sr (m := 265093120) (by decide) (join_su (m := 190054400) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 262307840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 190054400) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 267878400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 265093120) (by decide) (join_su (m := 192675840) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 262307840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 192675840) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 267878400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (9/40 : ℝ) (37/160 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((188743680 : ℤ) : ℝ) / (D : ℝ)) = (9/40 : ℝ) := by norm_num [D]
  have e1 : (((193986560 : ℤ) : ℝ) / (D : ℝ)) = (37/160 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
