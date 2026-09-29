-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r208404480_256901120
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T09:28:28.788535+00:00
-- url     : https://prove2.me/submissions/e8b8c425-1102-4600-a720-694b14ee214c

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [3/100, 1/25]`, `ρ ∈ [159/640, 49/160]` by 18 cells of the computing
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
theorem cell0 : cellOK 25165824 27262976 208404480 220528640 ⟨⟨305758852033, 305758852046⟩, ⟨279300769742, 333625435964⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 27262976 29360128 208404480 220528640 ⟨⟨298769769069, 298769769090⟩, ⟨273090571182, 325804147629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 25165824 27262976 220528640 232652800 ⟨⟨315349469684, 315349469697⟩, ⟨289253180274, 342755787843⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 27262976 29360128 220528640 232652800 ⟨⟨308377985348, 308377985368⟩, ⟨283023078275, 334996784632⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 29360128 31457280 208404480 214466560 ⟨⟨289649977096, 289649977117⟩, ⟨271112138321, 308920720549⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 29360128 31457280 214466560 220528640 ⟨⟨294537567272, 294537567289⟩, ⟨276097775200, 313686895069⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 31457280 33554432 208404480 214466560 ⟨⟨283283789912, 283283789932⟩, ⟨265259331203, 302014720629⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 31457280 33554432 214466560 220528640 ⟨⟨288167765605, 288167765624⟩, ⟨270229907316, 306790452284⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 29360128 31457280 220528640 232652800 ⟨⟨301718378250, 301718378267⟩, ⟨277062619781, 327593992175⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 31457280 33554432 220528640 232652800 ⟨⟨295346104441, 295346104460⟩, ⟨271351145618, 320518924198⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 25165824 27262976 232652800 244776960 ⟨⟨324627797569, 324627797581⟩, ⟨298881052940, 351594615021⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 27262976 29360128 232652800 244776960 ⟨⟨317678409112, 317678409133⟩, ⟨292638116681, 343898905425⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 25165824 27262976 244776960 256901120 ⟨⟨333621111237, 333621111250⟩, ⟨308211824423, 360168056190⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 27262976 29360128 244776960 256901120 ⟨⟨326697362638, 326697362654⟩, ⟨301961952863, 352536049000⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 29360128 31457280 232652800 244776960 ⟨⟨311029929610, 311029929626⟩, ⟨286657041021, 336544735465⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 31457280 33554432 232652800 244776960 ⟨⟨304659125598, 304659125614⟩, ⟨280918131107, 329505326202⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 29360128 31457280 244776960 256901120 ⟨⟨320064121667, 320064121683⟩, ⟨295966404508, 345231886030⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 31457280 33554432 244776960 256901120 ⟨⟨313699349052, 313699349070⟩, ⟨290206377127, 338230324003⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 25165824 33554432 208404480 256901120 t = true :=
  ⟨_, (join_sr (m := 232652800) (by decide) (join_su (m := 29360128) (by decide) (join_sr (m := 220528640) (by decide) (join_su (m := 27262976) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 27262976) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 220528640) (by decide) (join_su (m := 31457280) (by decide) (join_sr (m := 214466560) (by decide) (leaf_ok cell4) (leaf_ok cell5)) (join_sr (m := 214466560) (by decide) (leaf_ok cell6) (leaf_ok cell7))) (join_su (m := 31457280) (by decide) (leaf_ok cell8) (leaf_ok cell9)))) (join_su (m := 29360128) (by decide) (join_sr (m := 244776960) (by decide) (join_su (m := 27262976) (by decide) (leaf_ok cell10) (leaf_ok cell11)) (join_su (m := 27262976) (by decide) (leaf_ok cell12) (leaf_ok cell13))) (join_sr (m := 244776960) (by decide) (join_su (m := 31457280) (by decide) (leaf_ok cell14) (leaf_ok cell15)) (join_su (m := 31457280) (by decide) (leaf_ok cell16) (leaf_ok cell17)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (159/640 : ℝ) (49/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((25165824 : ℤ) : ℝ) / (D : ℝ)) = (3/100 : ℝ) := by norm_num [D]
  have e1 : (((33554432 : ℤ) : ℝ) / (D : ℝ)) = (1/25 : ℝ) := by norm_num [D]
  have e2 : (((208404480 : ℤ) : ℝ) / (D : ℝ)) = (159/640 : ℝ) := by norm_num [D]
  have e3 : (((256901120 : ℤ) : ℝ) / (D : ℝ)) = (49/160 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
