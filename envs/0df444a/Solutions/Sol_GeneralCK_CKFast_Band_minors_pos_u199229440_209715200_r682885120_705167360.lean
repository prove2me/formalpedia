-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u199229440_209715200_r682885120_705167360
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T04:03:54.675378+00:00
-- url     : https://prove2.me/submissions/7d7a8270-8a58-4f41-9c1d-86162e7dab60

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [19/80, 1/4]`, `ρ ∈ [521/640, 269/320]` by 10 cells of the computing
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
theorem cell0 : cellOK 199229440 201850880 682885120 694026240 ⟨⟨253324904216, 253324904226⟩, ⟨242685999096, 264190849505⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 201850880 204472320 682885120 694026240 ⟨⟨249824247201, 249824247206⟩, ⟨239280275088, 260594318330⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 199229440 201850880 694026240 705167360 ⟨⟨256990098284, 256990098292⟩, ⟨246295704061, 267910422173⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 201850880 204472320 694026240 705167360 ⟨⟨253450019628, 253450019631⟩, ⟨242850369230, 264274743729⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 204472320 207093760 682885120 694026240 ⟨⟨246342986437, 246342986447⟩, ⟨235893095811, 257018013601⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 207093760 209715200 682885120 688455680 ⟨⟨241993100545, 241993100555⟩, ⟨233047336425, 251103144812⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 207093760 209715200 688455680 694026240 ⟨⟨243767895894, 243767895904⟩, ⟨234795512704, 252904346792⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 204472320 207093760 694026240 705167360 ⟨⟨249929117596, 249929117605⟩, ⟨239423387343, 260659041930⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 207093760 209715200 694026240 699596800 ⟨⟨245541031115, 245541031124⟩, ⟨236542050543, 254703861864⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 207093760 209715200 699596800 705167360 ⟨⟨247312532827, 247312532836⟩, ⟨238286976069, 256501717127⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 199229440 209715200 682885120 705167360 t = true :=
  ⟨_, (join_su (m := 204472320) (by decide) (join_sr (m := 694026240) (by decide) (join_su (m := 201850880) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (join_su (m := 201850880) (by decide) (leaf_ok cell2) (leaf_ok cell3))) (join_sr (m := 694026240) (by decide) (join_su (m := 207093760) (by decide) (leaf_ok cell4) (join_sr (m := 688455680) (by decide) (leaf_ok cell5) (leaf_ok cell6))) (join_su (m := 207093760) (by decide) (leaf_ok cell7) (join_sr (m := 699596800) (by decide) (leaf_ok cell8) (leaf_ok cell9)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (19/80 : ℝ) (1/4 : ℝ) →
    rho ∈ Set.Icc (521/640 : ℝ) (269/320 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((199229440 : ℤ) : ℝ) / (D : ℝ)) = (19/80 : ℝ) := by norm_num [D]
  have e1 : (((209715200 : ℤ) : ℝ) / (D : ℝ)) = (1/4 : ℝ) := by norm_num [D]
  have e2 : (((682885120 : ℤ) : ℝ) / (D : ℝ)) = (521/640 : ℝ) := by norm_num [D]
  have e3 : (((705167360 : ℤ) : ℝ) / (D : ℝ)) = (269/320 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
