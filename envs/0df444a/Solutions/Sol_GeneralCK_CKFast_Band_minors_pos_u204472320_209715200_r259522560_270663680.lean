-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u204472320_209715200_r259522560_270663680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T03:33:44.952598+00:00
-- url     : https://prove2.me/submissions/c61cfa6a-8047-4de8-afea-86b9a187afa4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [39/160, 1/4]`, `ρ ∈ [99/320, 413/1280]` by 16 cells of the computing
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
theorem cell0 : cellOK 204472320 205783040 259522560 262307840 ⟨⟨101485631429, 101485631435⟩, ⟨98019700429, 104993869185⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 204472320 205783040 262307840 265093120 ⟨⟨102502411976, 102502411984⟩, ⟨99028905940, 106018240326⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 205783040 207093760 259522560 262307840 ⟨⟨100659084814, 100659084815⟩, ⟨97209497941, 104150693407⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 205783040 207093760 262307840 265093120 ⟨⟨101668572091, 101668572096⟩, ⟨98211435123, 105167747589⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 205783040 265093120 267878400 ⟨⟨103518027911, 103518027918⟩, ⟨100036956767, 107041436617⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 204472320 205783040 267878400 270663680 ⟨⟨104532485824, 104532485832⟩, ⟨101043859440, 108063464715⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 205783040 207093760 265093120 267878400 ⟨⟨102676919939, 102676919944⟩, ⟨99212242441, 106183652469⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 205783040 207093760 267878400 270663680 ⟨⟨103684134765, 103684134770⟩, ⟨100211926247, 107198414518⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 208404480 259522560 262307840 ⟨⟨99837351058, 99837351064⟩, ⟨96403946706, 103312495661⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207093760 208404480 262307840 265093120 ⟨⟨100839565740, 100839565747⟩, ⟨97398636503, 104322253251⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 208404480 209715200 259522560 262307840 ⟨⟨99020360989, 99020360997⟩, ⟨95602979961, 102479204297⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 208404480 209715200 262307840 265093120 ⟨⟨100015323616, 100015323624⟩, ⟨96590443176, 103481685543⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 207093760 208404480 265093120 267878400 ⟨⟨101840665727, 101840665733⟩, ⟨98392220817, 105330886635⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 207093760 208404480 267878400 270663680 ⟨⟨102840657249, 102840657257⟩, ⟨99384705825, 106338402101⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 208404480 209715200 265093120 267878400 ⟨⟨101009195845, 101009195852⟩, ⟨97576824856, 104483067232⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 208404480 209715200 267878400 270663680 ⟨⟨102001983731, 102001983739⟩, ⟨98562131008, 105483355475⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 204472320 209715200 259522560 270663680 t = true :=
  ⟨_, (join_su (m := 207093760) (by decide) (join_sr (m := 265093120) (by decide) (join_su (m := 205783040) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 262307840) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 205783040) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 267878400) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 265093120) (by decide) (join_su (m := 208404480) (by decide) (join_sr (m := 262307840) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 262307840) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 208404480) (by decide) (join_sr (m := 267878400) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 267878400) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (39/160 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (99/320 : ℝ) (413/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((204472320 : ℤ) : ℝ) / (D : ℝ)) = (39/160 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((259522560 : ℤ) : ℝ) / (D : ℝ)) = (99/320 : ℝ) := by norm_num [D]
  have e3 : (((270663680 : ℤ) : ℝ) / (D : ℝ)) = (413/1280 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
