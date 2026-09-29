-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_220200960_r682885120_705167360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T08:03:25.966982+00:00
-- url     : https://prove2.me/submissions/7b2eb552-f21c-45f4-b1ed-4f406a9285e4

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [1/4, 21/80]`, `ρ ∈ [521/640, 269/320]` by 16 cells of the computing
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
theorem cell0 : cellOK 209715200 212336640 682885120 688455680 ⟨⟨238559449996, 238559450005⟩, ⟨229681343888, 247601416088⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 209715200 212336640 688455680 694026240 ⟨⟨240314156271, 240314156280⟩, ⟨231409387112, 249382600178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 212336640 214958080 682885120 688455680 ⟨⟨235144028780, 235144028789⟩, ⟨226332991763, 244118493418⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 212336640 214958080 688455680 694026240 ⟨⟨236878547369, 236878547379⟩, ⟨228040813795, 245879549832⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 209715200 212336640 694026240 699596800 ⟨⟨242067261503, 242067261512⟩, ⟨233135849136, 251162158380⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 209715200 212336640 699596800 705167360 ⟨⟨243818791232, 243818791241⟩, ⟨234860755033, 252940116688⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 212336640 214958080 694026240 699596800 ⟨⟨238611522716, 238611522727⟩, ⟨229747110600, 247639040082⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 212336640 214958080 699596800 705167360 ⟨⟨240342979318, 240342979327⟩, ⟨231451906230, 249396989089⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 214958080 217579520 682885120 688455680 ⟨⟨231746447669, 231746447671⟩, ⟨223001900775, 240653978153⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 214958080 217579520 688455680 694026240 ⟨⟨233460683059, 233460683064⟩, ⟨224689416306, 242394800488⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 217579520 220200960 682885120 688455680 ⟨⟨228366325768, 228366325777⟩, ⟨219687699782, 237207480202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 217579520 220200960 688455680 694026240 ⟨⟨230060185449, 230060185458⟩, ⟨221354826240, 238927965328⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 214958080 217579520 694026240 699596800 ⟨⟨235173431726, 235173431731⟩, ⟨226375461323, 244134115081⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 214958080 217579520 699596800 705167360 ⟨⟨236884717151, 236884717155⟩, ⟨228060058883, 245871945814⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 217579520 220200960 694026240 699596800 ⟨⟨231752613643, 231752613652⟩, ⟨223020535636, 240646999836⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 217579520 220200960 699596800 705167360 ⟨⟨233443632848, 233443632857⟩, ⟨224684850069, 242364606599⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 209715200 220200960 682885120 705167360 t = true :=
  ⟨_, (join_su (m := 214958080) (by decide) (join_sr (m := 694026240) (by decide) (join_su (m := 212336640) (by decide) (join_sr (m := 688455680) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_sr (m := 688455680) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_su (m := 212336640) (by decide) (join_sr (m := 699596800) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 699596800) (by decide) (leaf_ok cell6) (leaf_ok cell7)))) (join_sr (m := 694026240) (by decide) (join_su (m := 217579520) (by decide) (join_sr (m := 688455680) (by decide) (leaf_ok cell8) (leaf_ok cell9)) (join_sr (m := 688455680) (by decide) (leaf_ok cell10) (leaf_ok cell11))) (join_su (m := 217579520) (by decide) (join_sr (m := 699596800) (by decide) (leaf_ok cell12) (leaf_ok cell13)) (join_sr (m := 699596800) (by decide) (leaf_ok cell14) (leaf_ok cell15)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (21/80 : ℝ) →
    rho ∈ Set.Icc (521/640 : ℝ) (269/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e1 : (((220200960 : ℤ) : ℝ) / (D : ℝ)) = (21/80 : ℝ) := by norm_num [D]
  have e2 : (((682885120 : ℤ) : ℝ) / (D : ℝ)) = (521/640 : ℝ) := by norm_num [D]
  have e3 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
